from z3 import *
from pathlib import Path
from timeit import default_timer as timer
import re
import sys

# Check for GUI flag
import argparse
import tkinter as tk
from tkinter import ttk, messagebox
from tkinter import filedialog

class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.total_exam_days = 1  # Total days exams can be conducted
        self.max_exams_per_room_per_day = 1  # Limit exams per room per day
        self.room_capacities = []
        self.exams_to_students = []
        self.student_exam_capacity = []

def read_file(filename):
    def read_attribute(name):
        line = f.readline()
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception("Could not parse line {line}; expected the {name} attribute")

    instance = Instance()
    with open(filename) as f:
        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams = read_attribute("Number of exams")
        instance.number_of_slots = read_attribute("Number of slots")
        instance.number_of_rooms = read_attribute("Number of rooms")
        instance.total_exam_days = 1
        instance.max_exams_per_room_per_day = 1

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))

        while True:
            l = f.readline()
            if l == "":
                break
            m = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', l)
            if m:
                instance.exams_to_students.append((int(m.group(1)), int(m.group(2))))
            else:
                raise Exception(f'Failed to parse this line: {l}')

        # create an empty array for the number of exams
        for r in range(instance.number_of_exams):
            instance.student_exam_capacity.append(0)

        # increment the number of students in an exam
        for r in instance.exams_to_students:
            instance.student_exam_capacity[r[0]] += 1
    return instance


def solve(instance, find_all_solutions=True):
    # Start timer
    start_solve = timer()

    s = Solver()

   # Declaration
    exam = Int('exam')
    room = Int('room')
    ts = Int('ts')
    nex = Int('nex')
    nts = Int('nts')
    student = Int('student')
    exam_day = Int('exam_day')  # New variable for day assignment

    # Ranges
    Student_Range = Function('Student_Range', IntSort(), BoolSort())
    Exam_Range = Function('Exam_Range', IntSort(), BoolSort())
    Room_Range = Function('Room_Range', IntSort(), BoolSort())
    TimeSlot_Range = Function('TimeSlot_Range', IntSort(), BoolSort())
    ExamDay_Range = Function('ExamDay_Range', IntSort(), BoolSort())

    # Range constraints
    s.add(ForAll([student], Student_Range(student) == And(student >= 0, student < instance.number_of_students)))
    s.add(ForAll([exam], Exam_Range(exam) == And(exam >= 0, exam < instance.number_of_exams)))
    s.add(ForAll([ts], TimeSlot_Range(ts) == And(ts >= 0, ts < instance.number_of_slots)))
    s.add(ForAll([room], Room_Range(room) == And(room >= 0, room < instance.number_of_rooms)))
    s.add(ForAll([exam_day], ExamDay_Range(exam_day) == And(exam_day >= 0, exam_day < instance.total_exam_days)))  # Assuming one day per slot

    # Functions
    ExamRoom = Function('ExamRoom', IntSort(), IntSort())
    ExamTime = Function('ExamTime', IntSort(), IntSort())
    ExamStudent = Function('ExamStudent', IntSort(), IntSort(), BoolSort())
    ExamDay = Function('ExamDay', IntSort(), IntSort())  # Maps each exam to a day

    # Student assignments
    for etos in instance.exams_to_students:
        s.add(ExamStudent(etos[0], etos[1]))

    # Constraints
    # First and second constraint
    s.add(
        ForAll([exam],
               Implies(
                   Exam_Range(exam),
                   Exists([room, ts],
                          And(Room_Range(room),
                              TimeSlot_Range(ts),
                              ExamTime(exam) == ts,
                              ExamRoom(exam) == room,
                              ForAll([nex],
                                     Implies(
                                         Exam_Range(nex),
                                         Implies(
                                             And(
                                                 ExamRoom(nex) == room,
                                                 ExamTime(nex) == ts
                                             ),
                                             exam == nex
                                         )
                                     )
                                     )
                              )
                          )
               )
               )
    )

    # Third constraint
    for ex2 in range(instance.number_of_exams):
        for rm2 in range(instance.number_of_rooms):
            s.add(Implies((ExamRoom(ex2) == rm2), instance.student_exam_capacity[ex2] <= instance.room_capacities[rm2]))

    # Fourth constraint
    s.add(
        ForAll(
            [student, nex, ts, nts, exam],
            Implies(
                And(
                    Student_Range(student),
                    Exam_Range(exam),
                    Exam_Range(nex),
                    TimeSlot_Range(ts),
                    TimeSlot_Range(nts),
                    Not((exam == nex))
                ),
                Implies(
                    And(
                        ExamTime(exam) == ts,
                        ExamTime(nex) == nts,
                        ExamStudent(exam, student),
                        ExamStudent(nex, student)
                    ),
                    And(
                        (ts + 1 != nts),
                        (ts - 1 != nts),
                        (ts != nts)
                    )
                )
            )
        )
    )

    # Fifth Constraint (ExamDay): Ensures that each exam is mapped to a day in the specified ExamDay_Range
    s.add(
        ForAll(
            [exam],
            Implies(
                Exam_Range(exam),
                Exists(
                    [exam_day],
                    And(
                        ExamDay_Range(exam_day),
                        ExamDay(exam) == exam_day
                    )
                )
            )
        )
    )

    # Sixth Constraint (MaximumExamsPerRoomPerDay): Limit Exams Per Room Per Day
    s.add(
        ForAll(
            [room, exam_day],
            Implies(
                And(
                    Room_Range(room),
                    ExamDay_Range(exam_day)
                ),
                Sum([
                    If(And(ExamRoom(exam) == room, ExamDay(exam) == exam_day), 1, 0)
                    for exam in range(instance.number_of_exams)
                ]) <= instance.max_exams_per_room_per_day
            )
        )
    )

    solutions = []
    output_text = ""
    total_solve_time = 0

    while True:
        start_iter = timer()
        if s.check() == unsat:
            end_iter = timer()
            total_solve_time += end_iter - start_iter
            if not solutions:
                output_text += 'unsat\n'
            else:
                output_text += 'All solutions found.\n'
            break
        else:
            m = s.model()
            end_iter = timer()
            total_solve_time += end_iter - start_iter
            result = []
            for ex2 in range(instance.number_of_exams):
                res_dict = {
                    'Exam': ex2,
                    'Room': m.eval(ExamRoom(ex2)).as_long(),
                    'Slot': m.eval(ExamTime(ex2)).as_long(),
                    'Day': m.eval(ExamDay(ex2)).as_long()
                }
                result.append(res_dict)

            # Add the solution to the list
            solutions.append(result)

            # Stop after finding the first solution if not finding all
            if not find_all_solutions:
                output_text += 'Found one solution.\n'
                break

            # Build the blocking clause to prevent this solution from being found again
            block = []
            for ex2 in range(instance.number_of_exams):
                block.append(
                    And(
                        ExamRoom(ex2) == m.eval(ExamRoom(ex2)),
                        ExamTime(ex2) == m.eval(ExamTime(ex2)),
                        ExamDay(ex2) == m.eval(ExamDay(ex2))
                    )
                )
            s.add(Not(And(block)))

    # End timer
    end_solve = timer()
    solve_time = end_solve - start_solve

    return solutions, solve_time, output_text

# GUI Implementation
def run_gui():
    class App(tk.Tk):
        def __init__(self):
            super().__init__()
            self.title("Exam Scheduler")
            self.state("zoomed")
            self.instance = Instance()
            self.phase = 1
            self.widgets = {}

            # Create canvas and container for global scrolling
            self.canvas = tk.Canvas(self)
            self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

            self.scrollbar = tk.Scrollbar(self, command=self.canvas.yview)
            self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

            self.canvas.configure(yscrollcommand=self.scrollbar.set)

            self.container = tk.Frame(self.canvas)
            self.container.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
            self.canvas.create_window((0, 0), window=self.container, anchor="nw")

            # Initialize first phase widgets
            self.create_phase1_widgets()

        def clear_widgets(self):
            """Destroy all widgets in the container."""
            for widget in self.container.winfo_children():
                widget.destroy()
            self.widgets = {}

        # **Updated create_phase1_widgets method with file selection option**
        def create_phase1_widgets(self):
            self.clear_widgets()
            self.container.grid_rowconfigure(0, weight=1)
            self.container.grid_columnconfigure(0, weight=1)

            phase_frame = tk.Frame(self.container)
            phase_frame.grid(row=0, column=0, sticky="nsew")
            phase_frame.grid_rowconfigure(0, weight=1)
            phase_frame.grid_columnconfigure(0, weight=1)

            # Add widgets to phase_frame
            phase_label = tk.Label(phase_frame, text="Phase 1: Enter Basic Information", font=("Arial", 14))
            phase_label.pack(pady=10)

            # Checkbox for finding all solutions
            self.find_all_var = tk.BooleanVar(value=True)
            find_all_checkbox = tk.Checkbutton(phase_frame, text="Find all possible solutions", variable=self.find_all_var)
            find_all_checkbox.pack(pady=5)

            # **Option to select a file**
            file_label = tk.Label(phase_frame, text="Or select a .txt file to load data:")
            file_label.pack(pady=5)
            file_button = tk.Button(phase_frame, text="Select File", command=self.select_file)
            file_button.pack(pady=5)

            # Number of students
            num_students_label = tk.Label(phase_frame, text="Number of students:")
            num_students_entry = tk.Entry(phase_frame)
            num_students_label.pack(pady=5)
            num_students_entry.pack(pady=5)

            # Number of exams
            num_exams_label = tk.Label(phase_frame, text="Number of exams:")
            num_exams_entry = tk.Entry(phase_frame)
            num_exams_label.pack(pady=5)
            num_exams_entry.pack(pady=5)

            # Number of slots
            num_slots_label = tk.Label(phase_frame, text="Number of timeslots:")
            num_slots_entry = tk.Entry(phase_frame)
            num_slots_label.pack(pady=5)
            num_slots_entry.pack(pady=5)

            # Number of rooms
            num_rooms_label = tk.Label(phase_frame, text="Number of rooms:")
            num_rooms_entry = tk.Entry(phase_frame)
            num_rooms_label.pack(pady=5)
            num_rooms_entry.pack(pady=5)

            # Total exam days
            total_days_label = tk.Label(phase_frame, text="Total exam days:")
            total_days_entry = tk.Entry(phase_frame)
            total_days_label.pack(pady=5)
            total_days_entry.pack(pady=5)

            # Max exams per room per day
            max_exams_label = tk.Label(phase_frame, text="Max exams per room per day:")
            max_exams_entry = tk.Entry(phase_frame)
            max_exams_label.pack(pady=5)
            max_exams_entry.pack(pady=5)

            # Next button
            next_button = tk.Button(phase_frame, text="Next", command=lambda: self.phase1_next(
                num_students_entry.get(),
                num_exams_entry.get(),
                num_rooms_entry.get(),
                num_slots_entry.get(),
                total_days_entry.get(),
                max_exams_entry.get()
            ))
            next_button.pack(pady=10)

        # **New method to select a file and read data**
        def select_file(self):
            filename = filedialog.askopenfilename(
                title="Select a .txt file",
                filetypes=(("Text files", "*.txt"),)
            )
            if filename:
                try:
                    self.instance = read_file(filename)
                    self.phase4_solve()
                except Exception as e:
                    messagebox.showerror("Error", f"Failed to read file: {e}")

        def phase1_next(self, num_students, num_exams, num_rooms, num_slots, total_days, max_exams):
            try:
                self.instance.number_of_students = int(num_students)
                self.instance.number_of_exams = int(num_exams)
                self.instance.number_of_rooms = int(num_rooms)
                self.instance.number_of_slots = int(num_slots)
                self.instance.total_exam_days = int(total_days)
                self.instance.max_exams_per_room_per_day = int(max_exams)
                self.create_phase2_widgets()
            except ValueError:
                messagebox.showerror("Invalid input", "Please enter valid integers.")

        def create_phase2_widgets(self):
            self.clear_widgets()
            self.container.grid_rowconfigure(0, weight=1)
            self.container.grid_columnconfigure(0, weight=1)

            phase_frame = tk.Frame(self.container)
            phase_frame.grid(row=0, column=0, sticky="nsew")
            phase_frame.grid_rowconfigure(0, weight=1)
            phase_frame.grid_columnconfigure(0, weight=1)

            phase_label = tk.Label(phase_frame, text="Phase 2: Enter Room Capacities", font=("Arial", 14))
            phase_label.pack(pady=10)

            self.room_capacity_entries = []
            for i in range(self.instance.number_of_rooms):
                label = tk.Label(phase_frame, text=f"Room {i} capacity:")
                entry = tk.Entry(phase_frame)
                label.pack(pady=5)
                entry.pack(pady=5)
                self.room_capacity_entries.append(entry)

            next_button = tk.Button(phase_frame, text="Next", command=self.phase2_next)
            next_button.pack(pady=10)


        def phase2_next(self):
            try:
                self.instance.room_capacities = []
                for entry in self.room_capacity_entries:
                    capacity = int(entry.get())
                    self.instance.room_capacities.append(capacity)
                self.create_phase3_widgets()
            except ValueError:
                messagebox.showerror("Invalid input", "Please enter valid integers.")


        def create_phase3_widgets(self):
            self.clear_widgets()
            self.container.grid_rowconfigure(0, weight=1)
            self.container.grid_columnconfigure(0, weight=1)

            phase_frame = tk.Frame(self.container)
            phase_frame.grid(row=0, column=0, sticky="nsew")
            phase_frame.grid_rowconfigure(0, weight=1)
            phase_frame.grid_columnconfigure(0, weight=1)

            phase_label = tk.Label(phase_frame, text="Phase 3: Assign Students to Exams", font=("Arial", 14))
            phase_label.pack(pady=10)

            canvas = tk.Canvas(phase_frame)
            canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

            scrollbar = tk.Scrollbar(phase_frame, command=canvas.yview)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

            canvas.configure(yscrollcommand=scrollbar.set)

            frame = tk.Frame(canvas)
            canvas.create_window((0, 0), window=frame, anchor='nw')

            self.checkbutton_vars = {}
            for s in range(self.instance.number_of_students):
                self.checkbutton_vars[s] = {}

            # Header row for exams
            tk.Label(frame, text="Student/Exam").grid(row=0, column=0, sticky='w')
            for e in range(self.instance.number_of_exams):
                tk.Label(frame, text=f"Exam {e}").grid(row=0, column=e + 1)

            # Rows for students and checkbuttons
            for s in range(self.instance.number_of_students):
                tk.Label(frame, text=f"Student {s}").grid(row=s + 1, column=0, sticky='w')
                for e in range(self.instance.number_of_exams):
                    var = tk.IntVar()
                    self.checkbutton_vars[s][e] = var
                    tk.Checkbutton(frame, variable=var).grid(row=s + 1, column=e + 1)

            next_button = tk.Button(phase_frame, text="Solve", command=self.phase3_next)
            next_button.pack(pady=10)

        def phase3_next(self):
            """Handle the submission of student-exam assignments and solve the problem."""
            self.instance.exams_to_students = []
            self.instance.student_exam_capacity = [0] * self.instance.number_of_exams
            for s in range(self.instance.number_of_students):
                for e in range(self.instance.number_of_exams):
                    if self.checkbutton_vars[s][e].get() == 1:
                        self.instance.exams_to_students.append((e, s))
                        self.instance.student_exam_capacity[e] += 1
            self.phase4_solve()


        def phase4_solve(self):
            self.clear_widgets()
            phase_frame = tk.Frame(self.container)
            phase_frame.pack(pady=10)
            phase_label = tk.Label(phase_frame, text="Phase 4: Solution", font=("Arial", 16, "bold"))
            phase_label.pack()
            self.widgets['phase_label'] = phase_label

            # Get the checkbox value for finding all solutions
            find_all_solutions = self.find_all_var.get()

            # Solve the problem and get the results
            solutions, solve_time, output_text = solve(self.instance, find_all_solutions=find_all_solutions)

            # Display solve time and number of solutions
            time_label = tk.Label(phase_frame, text=f"Solved in {solve_time:.3f} seconds, found {len(solutions)} solution(s)", font=("Arial", 12, "italic"))
            time_label.pack(anchor='w', padx=10)
            self.widgets['time_label'] = time_label

            if not solutions:
                # If no solution is found
                result_label = tk.Label(phase_frame, text="No solution found.", font=("Arial", 14, "bold"))
                result_label.pack(pady=10)
                self.widgets['result_label'] = result_label
            else:
                # Store the solutions
                self.solutions = solutions
                self.current_solution_index = 0  # Start with the first solution

                # Dropdown menu to select solution
                selection_frame = tk.Frame(phase_frame)
                selection_frame.pack(pady=10)

                solution_label = tk.Label(selection_frame, text="Select Solution:")
                solution_label.pack(side=tk.LEFT)

                solution_numbers = [f"Solution {i+1}" for i in range(len(solutions))]
                self.solution_var = tk.StringVar()
                self.solution_var.set(solution_numbers[0])  # Set default value

                solution_menu = ttk.Combobox(selection_frame, textvariable=self.solution_var, values=solution_numbers, state="readonly")
                solution_menu.pack(side=tk.LEFT)
                solution_menu.bind("<<ComboboxSelected>>", self.update_solution_display)

                # Initial display of the first solution
                self.display_solution(solutions[0])

        
        def update_solution_display(self, event):
            # Get the selected solution index
            selected = self.solution_var.get()
            index = int(selected.split()[1]) - 1  # "Solution 1" -> index 0
            self.current_solution_index = index
            # Clear previous timetables
            self.clear_timetable_widgets()
            # Display the selected solution
            self.display_solution(self.solutions[index])

        def clear_timetable_widgets(self):
            # Destroy timetable widgets
            if 'notebook' in self.widgets:
                self.widgets['notebook'].destroy()
                # Remove other timetable-related widgets if any

        def display_solution(self, result):
            # Notebook for different timetable sections
            notebook = ttk.Notebook(self.container)
            notebook.pack(fill=tk.BOTH, expand=True, pady=10)
            self.widgets['notebook'] = notebook

            # Student Timetables Tab
            student_frame = tk.Frame(notebook)
            notebook.add(student_frame, text="Student Timetables")
            student_notebook = ttk.Notebook(student_frame)
            student_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            for student in range(self.instance.number_of_students):
                frame = tk.Frame(student_notebook)
                student_notebook.add(frame, text=f"Student {student}")

                tree = ttk.Treeview(frame)
                tree['columns'] = ('Exam', 'Room', 'Slot', 'Day')
                tree.column("#0", width=0, stretch=tk.NO)
                tree.column("Exam", anchor=tk.CENTER, width=80)
                tree.column("Room", anchor=tk.CENTER, width=80)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Day", anchor=tk.CENTER, width=80)

                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Exam", text="Exam", anchor=tk.CENTER)
                tree.heading("Room", text="Room", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Day", text="Day", anchor=tk.CENTER)

                for exam, assigned_student in self.instance.exams_to_students:
                    if assigned_student == student:
                        exam_info = next((r for r in result if r['Exam'] == exam), None)
                        if exam_info:
                            tree.insert(parent='', index='end', text='',
                                        values=(exam, exam_info['Room'], exam_info['Slot'], exam_info['Day']))

                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'student_{student}_tree'] = tree

            # Exam Timetables Tab
            exam_frame = tk.Frame(notebook)
            notebook.add(exam_frame, text="Exam Timetables")
            exam_notebook = ttk.Notebook(exam_frame)
            exam_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            for exam in range(self.instance.number_of_exams):
                frame = tk.Frame(exam_notebook)
                exam_notebook.add(frame, text=f"Exam {exam}")

                tree = ttk.Treeview(frame)
                tree['columns'] = ('Student', 'Room', 'Slot', 'Day')
                tree.column("#0", width=0, stretch=tk.NO)
                tree.column("Student", anchor=tk.CENTER, width=80)
                tree.column("Room", anchor=tk.CENTER, width=80)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Day", anchor=tk.CENTER, width=80)

                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Student", text="Student", anchor=tk.CENTER)
                tree.heading("Room", text="Room", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Day", text="Day", anchor=tk.CENTER)

                exam_info = next((r for r in result if r['Exam'] == exam), None)
                if exam_info:
                    for exam_student, student in self.instance.exams_to_students:
                        if exam_student == exam:
                            tree.insert(parent='', index='end', text='',
                                        values=(student, exam_info['Room'], exam_info['Slot'], exam_info['Day']))

                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'exam_{exam}_tree'] = tree

            # Room Timetables Tab
            room_frame = tk.Frame(notebook)
            notebook.add(room_frame, text="Room Timetables")
            room_notebook = ttk.Notebook(room_frame)
            room_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            for room in range(self.instance.number_of_rooms):
                frame = tk.Frame(room_notebook)
                room_notebook.add(frame, text=f"Room {room}")

                tree = ttk.Treeview(frame)
                tree['columns'] = ('Exam', 'Slot', 'Day')
                tree.column("#0", width=0, stretch=tk.NO)
                tree.column("Exam", anchor=tk.CENTER, width=80)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Day", anchor=tk.CENTER, width=80)

                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Exam", text="Exam", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Day", text="Day", anchor=tk.CENTER)

                for res in result:
                    if res['Room'] == room:
                        tree.insert(parent='', index='end', text='',
                                    values=(res['Exam'], res['Slot'], res['Day']))

                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'room_{room}_tree'] = tree

            # Day Timetables Tab
            day_frame = tk.Frame(notebook)
            notebook.add(day_frame, text="Day Timetables")
            day_notebook = ttk.Notebook(day_frame)
            day_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            for day in range(self.instance.total_exam_days):
                frame = tk.Frame(day_notebook)
                day_notebook.add(frame, text=f"Day {day}")

                tree = ttk.Treeview(frame)
                tree['columns'] = ('Slot', 'Exam', 'Room')
                tree.column("#0", width=0, stretch=tk.NO)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Exam", anchor=tk.CENTER, width=80)
                tree.column("Room", anchor=tk.CENTER, width=80)

                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Exam", text="Exam", anchor=tk.CENTER)
                tree.heading("Room", text="Room", anchor=tk.CENTER)

                # Filter and sort results by slots for the current day
                day_slots = sorted([res for res in result if res['Day'] == day], key=lambda r: r['Slot'])
                for res in day_slots:
                    tree.insert(parent='', index='end', text='',
                                values=(res['Slot'], res['Exam'], res['Room']))

                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'day_{day}_tree'] = tree



    app = App()
    app.mainloop()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Exam Scheduler')
    parser.add_argument('--gui', action='store_true', help='Run with GUI')
    args = parser.parse_args()

    if args.gui:
        run_gui()
    else:
        # Get list of test files
        tests_dir = Path("test_instances")
        test_files = [file for file in tests_dir.iterdir() if file.is_file() and file.suffix == '.txt']

        # Print available test files
        print("Available test files:")
        for idx, test_file in enumerate(test_files):
            print(f"{idx+1}. {test_file.name}")

        # Ask user to select a file
        file_choice = int(input("Enter the number of the file you want to execute: "))

        if file_choice < 1 or file_choice > len(test_files):
            print("Invalid choice")
            sys.exit(1)

        selected_file = test_files[file_choice - 1]
        instance = read_file(str(selected_file))

        # Ask if user wants to print all solutions
        print_all = input("Do you want to print all solutions? (yes/no): ").strip().lower() == 'yes'

        # Solve the instance
        solutions, solve_time, output_text = solve(instance, find_all_solutions=print_all)

        print(f"Solved in {solve_time:.3f} seconds, found {len(solutions)} solution(s)")

        if print_all:
            # **Print solutions in batches of 100**
            batch_size = 100
            total_solutions = len(solutions)
            current_index = 0
            while current_index < total_solutions:
                end_index = min(current_index + batch_size, total_solutions)
                print(f"Printing solutions {current_index +1} to {end_index}:")
                for i in range(current_index, end_index):
                    print(f"Solution {i+1}:")
                    for res_dict in solutions[i]:
                        print(f"   Exam: {res_dict['Exam']}  Room: {res_dict['Room']}  Slot: {res_dict['Slot']}  Day: {res_dict['Day']}")
                    print("――――――――――――――――――――――――")
                current_index += batch_size
                if current_index < total_solutions:
                    more = input("Do you want to see the next batch of 100 solutions? (yes/no): ").strip().lower()
                    if more != 'yes':
                        break
        else:
            # Print the first solution
            if solutions:
                print("First solution:")
                for res_dict in solutions[0]:
                    print(f"   Exam: {res_dict['Exam']}  Room: {res_dict['Room']}  Slot: {res_dict['Slot']}  Day: {res_dict['Day']}")
            else:
                print("No solutions found.")
