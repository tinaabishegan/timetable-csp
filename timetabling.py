# Tinaabishegan Baladewan 
# 20408241
from z3 import *  # Importing Z3 solver for constraint satisfaction
from pathlib import Path  # Provides functionality for file path manipulations
from timeit import default_timer as timer  # Used for measuring execution time
import re  # Regular expression module for parsing
import sys  # System-specific parameters and functions
import argparse  # Used for parsing command-line arguments
import tkinter as tk  # Tkinter module for GUI implementation
from tkinter import ttk, messagebox  # Tkinter widgets and dialog utilities
from tkinter import filedialog  # Tkinter file dialog for selecting files

# Class to represent an instance of the scheduling problem
class Instance:
    def __init__(self):
        self.number_of_students = 0  # Number of students
        self.number_of_exams = 0  # Number of exams to schedule
        self.number_of_slots = 0  # Number of available timeslots
        self.number_of_rooms = 0  # Number of available rooms
        self.total_exam_days = 1  # Total days exams can be scheduled
        self.max_exams_per_room_per_day = 100  # Maximum exams allowed per room per day
        self.room_capacities = []  # List of room capacities
        self.exams_to_students = []  # Mapping of exams to students
        self.student_exam_capacity = []  # Number of students per exam

# Function to read problem instance data from a file
def read_file(filename):
    """
    Reads and parses an input file to populate an instance of the scheduling problem.
    :param filename: Path to the input file.
    :return: An Instance object populated with data from the file.
    """
    def read_attribute(name):
        """
        Reads a single attribute value from the file.
        :param name: Name of the attribute to read.
        :return: Integer value of the attribute.
        :raises Exception: If the line format does not match the expected pattern.
        """
        line = f.readline()
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))  # Extract and return the numeric value
        else:
            raise Exception(f"Could not parse line {line}; expected the {name} attribute")

    instance = Instance()  # Create an empty instance object
    with open(filename) as f:
        # Read basic attributes of the problem
        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams = read_attribute("Number of exams")
        instance.number_of_slots = read_attribute("Number of slots")
        instance.number_of_rooms = read_attribute("Number of rooms")
        
        # Default values for optional parameters
        instance.total_exam_days = 1  # Default: exams are conducted in 1 day
        instance.max_exams_per_room_per_day = 100  # Default: no practical limit

        # Read room capacities
        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))

        # Read mappings of exams to students
        while True:
            l = f.readline()  # Read the next line
            if l == "":  # Stop if end of file is reached
                break
            # Match lines that define an exam-to-student mapping
            m = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', l)
            if m:
                instance.exams_to_students.append((int(m.group(1)), int(m.group(2))))  # Append mapping
            else:
                raise Exception(f'Failed to parse this line: {l}')

        # Initialize the number of students assigned to each exam
        for r in range(instance.number_of_exams):
            instance.student_exam_capacity.append(0)

        # Count the number of students per exam based on the mappings
        for r in instance.exams_to_students:
            instance.student_exam_capacity[r[0]] += 1

    return instance  # Return the populated instance object


def solve(instance, find_all_solutions=True):
    """
    Solve the exam scheduling problem using Z3 constraints.
    :param instance: The problem instance containing all input parameters.
    :param find_all_solutions: Boolean flag to find one or all feasible solutions.
    :return: A list of solutions, total solve time, and output text summary.
    """
    # Start timer to measure total solving time
    start_solve = timer()

    # Create a Z3 solver instance
    s = Solver()

    # Declaration of Z3 integer variables for exams, rooms, timeslots, and students
    exam = Int('exam')  # Exam identifier
    room = Int('room')  # Room identifier
    ts = Int('ts')  # Timeslot identifier
    nex = Int('nex')  # Another exam variable (used for conflict constraints)
    nts = Int('nts')  # Another timeslot variable (used for conflict constraints)
    student = Int('student')  # Student identifier
    exam_day = Int('exam_day')  # Variable for day assignments for exams

    # Ranges: Boolean functions to define valid ranges for students, exams, rooms, etc.
    Student_Range = Function('Student_Range', IntSort(), BoolSort())
    Exam_Range = Function('Exam_Range', IntSort(), BoolSort())
    Room_Range = Function('Room_Range', IntSort(), BoolSort())
    TimeSlot_Range = Function('TimeSlot_Range', IntSort(), BoolSort())
    ExamDay_Range = Function('ExamDay_Range', IntSort(), BoolSort())

    # Add constraints to define the valid ranges for students, exams, rooms, timeslots, and days
    s.add(ForAll([student], Student_Range(student) == And(student >= 0, student < instance.number_of_students)))
    s.add(ForAll([exam], Exam_Range(exam) == And(exam >= 0, exam < instance.number_of_exams)))
    s.add(ForAll([ts], TimeSlot_Range(ts) == And(ts >= 0, ts < instance.number_of_slots)))
    s.add(ForAll([room], Room_Range(room) == And(room >= 0, room < instance.number_of_rooms)))
    s.add(ForAll([exam_day], ExamDay_Range(exam_day) == And(exam_day >= 0, exam_day < instance.total_exam_days)))

    # Functions to map exams to rooms, timeslots, students, and days
    ExamRoom = Function('ExamRoom', IntSort(), IntSort())  # Maps exam to room
    ExamTime = Function('ExamTime', IntSort(), IntSort())  # Maps exam to timeslot
    ExamStudent = Function('ExamStudent', IntSort(), IntSort(), BoolSort())  # Maps student to exams
    ExamDay = Function('ExamDay', IntSort(), IntSort())  # Maps exam to a day

    # Add constraints for student-to-exam assignments
    for etos in instance.exams_to_students:
        s.add(ExamStudent(etos[0], etos[1]))  # Exam etos[0] is taken by student etos[1]

    # Add constraints for room and timeslot assignments (Constraint 1 & 2)
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
                                             exam == nex  # Prevent conflicting assignments
                                         )
                                     )
                                     )
                              )
                          )
               )
               )
    )

    # Add capacity constraint (Constraint 3)
    for ex2 in range(instance.number_of_exams):
        for rm2 in range(instance.number_of_rooms):
            s.add(Implies((ExamRoom(ex2) == rm2), instance.student_exam_capacity[ex2] <= instance.room_capacities[rm2]))

    # Add constraints to avoid consecutive exams for a student (Constraint 4)
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
                    Not((exam == nex))  # Ensure exam and nex are different
                ),
                Implies(
                    And(
                        ExamTime(exam) == ts,
                        ExamTime(nex) == nts,
                        ExamStudent(exam, student),
                        ExamStudent(nex, student)
                    ),
                    And(
                        (ts + 1 != nts),  # Prevent consecutive timeslot assignments
                        (ts - 1 != nts),
                        (ts != nts)
                    )
                )
            )
        )
    )

    # Add day assignment constraint (Constraint 5)
    s.add(
        ForAll(
            [exam],
            Implies(
                Exam_Range(exam),
                Exists(
                    [exam_day],
                    And(
                        ExamDay_Range(exam_day),
                        ExamDay(exam) == exam_day  # Assign each exam to a valid day
                    )
                )
            )
        )
    )

    # Add limit on maximum exams per room per day (Constraint 6)
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

    # Initialize storage for solutions and solve time
    solutions = []
    output_text = ""
    total_solve_time = 0

    while True:
        start_iter = timer()  # Start measuring time for each iteration
        if s.check() == unsat:  # Check satisfiability of the constraints
            end_iter = timer()
            total_solve_time += end_iter - start_iter
            if not solutions:
                output_text += 'unsat\n'  # No solution found
            else:
                output_text += 'All solutions found.\n'  # All possible solutions have been explored
            break
        else:
            m = s.model()  # Retrieve a solution model
            end_iter = timer()
            total_solve_time += end_iter - start_iter
            result = []
            for ex2 in range(instance.number_of_exams):
                # Extract room, timeslot, and day assignments for each exam
                res_dict = {
                    'Exam': ex2,
                    'Room': m.eval(ExamRoom(ex2)).as_long(),
                    'Slot': m.eval(ExamTime(ex2)).as_long(),
                    'Day': m.eval(ExamDay(ex2)).as_long()
                }
                result.append(res_dict)

            # Store the solution
            solutions.append(result)

            # Stop after the first solution if not finding all solutions
            if not find_all_solutions:
                output_text += 'Found one solution.\n'
                break

            # Add a blocking clause to prevent rediscovery of the same solution
            block = []
            for ex2 in range(instance.number_of_exams):
                block.append(
                    And(
                        ExamRoom(ex2) == m.eval(ExamRoom(ex2)),
                        ExamTime(ex2) == m.eval(ExamTime(ex2)),
                        ExamDay(ex2) == m.eval(ExamDay(ex2))
                    )
                )
            s.add(Not(And(block)))  # Block the current solution

    # Stop timer
    end_solve = timer()
    solve_time = end_solve - start_solve

    # Return the solutions, total solve time, and output summary
    return solutions, solve_time, output_text


# GUI Implementation
def run_gui():
    class App(tk.Tk):
        def __init__(self):
            super().__init__()
            self.title("Exam Scheduler")  # Set the window title for the application
            self.state("zoomed")  # Open the window in maximized state
            self.instance = Instance()  # Create an instance to store user inputs
            self.phase = 1  # Variable to track the current phase (1-4) of input
            self.widgets = {}  # Dictionary to store references to widgets for easy access and updates

            # Create a canvas for adding widgets with scrolling support
            self.canvas = tk.Canvas(self)
            self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)  # Canvas fills the main window

            # Add a vertical scrollbar connected to the canvas
            self.scrollbar = tk.Scrollbar(self, command=self.canvas.yview)
            self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)  # Place the scrollbar to the right of the canvas

            self.canvas.configure(yscrollcommand=self.scrollbar.set)  # Synchronize canvas and scrollbar scrolling

            # Create a frame within the canvas to hold all widgets
            self.container = tk.Frame(self.canvas)
            # Adjust the canvas scrollable region when the container's size changes
            self.container.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
            self.canvas.create_window((0, 0), window=self.container, anchor="nw")  # Position the container at the top-left

            # Initialize the widgets for Phase 1 (basic information input)
            self.create_phase1_widgets()

        def clear_widgets(self):
            """Remove all widgets from the container."""
            for widget in self.container.winfo_children():
                widget.destroy()  # Destroy each widget in the container
            self.widgets = {}  # Reset the widgets dictionary

        # **Updated create_phase1_widgets method with file selection option**
        def create_phase1_widgets(self):
            """Create and display widgets for Phase 1: Entering basic exam details."""
            self.clear_widgets()  # Clear previous phase widgets
            self.container.grid_rowconfigure(0, weight=1)  # Ensure the container resizes properly
            self.container.grid_columnconfigure(0, weight=1)

            # Create a frame for Phase 1 widgets
            phase_frame = tk.Frame(self.container)
            phase_frame.grid(row=0, column=0, sticky="nsew")  # Fill the grid cell
            phase_frame.grid_rowconfigure(0, weight=1)
            phase_frame.grid_columnconfigure(0, weight=1)

            # Title label for Phase 1
            phase_label = tk.Label(phase_frame, text="Phase 1: Enter Basic Information", font=("Arial", 14))
            phase_label.pack(pady=10)

            # Checkbox for finding all possible solutions
            self.find_all_var = tk.BooleanVar(value=True)  # Variable to track checkbox state
            find_all_checkbox = tk.Checkbutton(phase_frame, text="Find all possible solutions", variable=self.find_all_var)
            find_all_checkbox.pack(pady=5)

            # Option to select a file for data input
            file_label = tk.Label(phase_frame, text="Or select a .txt file to load data:")
            file_label.pack(pady=5)
            file_button = tk.Button(phase_frame, text="Select File", command=self.select_file)
            file_button.pack(pady=5)

            # Input fields for basic information
            # Number of students input
            num_students_label = tk.Label(phase_frame, text="Number of students:")
            num_students_entry = tk.Entry(phase_frame)  # Text entry for number of students
            num_students_label.pack(pady=5)
            num_students_entry.pack(pady=5)

            # Number of exams input
            num_exams_label = tk.Label(phase_frame, text="Number of exams:")
            num_exams_entry = tk.Entry(phase_frame)  # Text entry for number of exams
            num_exams_label.pack(pady=5)
            num_exams_entry.pack(pady=5)

            # Number of timeslots input
            num_slots_label = tk.Label(phase_frame, text="Number of timeslots:")
            num_slots_entry = tk.Entry(phase_frame)  # Text entry for number of timeslots
            num_slots_label.pack(pady=5)
            num_slots_entry.pack(pady=5)

            # Number of rooms input
            num_rooms_label = tk.Label(phase_frame, text="Number of rooms:")
            num_rooms_entry = tk.Entry(phase_frame)  # Text entry for number of rooms
            num_rooms_label.pack(pady=5)
            num_rooms_entry.pack(pady=5)

            # Total exam days input
            total_days_label = tk.Label(phase_frame, text="Total exam days:")
            total_days_entry = tk.Entry(phase_frame)  # Text entry for total exam days
            total_days_label.pack(pady=5)
            total_days_entry.pack(pady=5)

            # Maximum exams per room per day input
            max_exams_label = tk.Label(phase_frame, text="Max exams per room per day:")
            max_exams_entry = tk.Entry(phase_frame)  # Text entry for max exams per room per day
            max_exams_label.pack(pady=5)
            max_exams_entry.pack(pady=5)

            # Button to proceed to the next phase with the entered inputs
            next_button = tk.Button(phase_frame, text="Next", command=lambda: self.phase1_next(
                num_students_entry.get(),  # Get the number of students from the entry
                num_exams_entry.get(),  # Get the number of exams
                num_rooms_entry.get(),  # Get the number of rooms
                num_slots_entry.get(),  # Get the number of timeslots
                total_days_entry.get(),  # Get the total exam days
                max_exams_entry.get()  # Get the max exams per room per day
            ))
            next_button.pack(pady=10)  # Add spacing around the button

        # **New method to select a file and read data**
        def select_file(self):
            """Allow the user to select a file containing input data and process it."""
            filename = filedialog.askopenfilename(
                title="Select a .txt file",
                filetypes=(("Text files", "*.txt"),)  # Only allow text files
            )
            if filename:
                try:
                    # Read the input data from the selected file and update the instance
                    self.instance = read_file(filename)
                    # Directly proceed to solving the problem
                    self.phase4_solve()
                except Exception as e:
                    # Show an error message if the file could not be read
                    messagebox.showerror("Error", f"Failed to read file: {e}")

        def phase1_next(self, num_students, num_exams, num_rooms, num_slots, total_days, max_exams):
            """Transition to Phase 2 after validating and storing basic input information."""
            try:
                # Convert and store user inputs as integers
                self.instance.number_of_students = int(num_students)
                self.instance.number_of_exams = int(num_exams)
                self.instance.number_of_rooms = int(num_rooms)
                self.instance.number_of_slots = int(num_slots)
                self.instance.total_exam_days = int(total_days)
                self.instance.max_exams_per_room_per_day = int(max_exams)
                # Proceed to Phase 2: Entering room capacities
                self.create_phase2_widgets()
            except ValueError:
                # Show an error message if any input is invalid
                messagebox.showerror("Invalid input", "Please enter valid integers.")

        def create_phase2_widgets(self):
            """Create and display widgets for Phase 2: Entering room capacities."""
            self.clear_widgets()  # Clear any existing widgets from Phase 1
            self.container.grid_rowconfigure(0, weight=1)
            self.container.grid_columnconfigure(0, weight=1)

            # Create a frame for Phase 2
            phase_frame = tk.Frame(self.container)
            phase_frame.grid(row=0, column=0, sticky="nsew")
            phase_frame.grid_rowconfigure(0, weight=1)
            phase_frame.grid_columnconfigure(0, weight=1)

            # Title for Phase 2
            phase_label = tk.Label(phase_frame, text="Phase 2: Enter Room Capacities", font=("Arial", 14))
            phase_label.pack(pady=10)

            # Input fields for room capacities
            self.room_capacity_entries = []  # List to hold capacity entry widgets
            for i in range(self.instance.number_of_rooms):
                # Label and entry field for each room's capacity
                label = tk.Label(phase_frame, text=f"Room {i} capacity:")
                entry = tk.Entry(phase_frame)
                label.pack(pady=5)
                entry.pack(pady=5)
                self.room_capacity_entries.append(entry)

            # Button to proceed to the next phase
            next_button = tk.Button(phase_frame, text="Next", command=self.phase2_next)
            next_button.pack(pady=10)

        def phase2_next(self):
            """Validate and store room capacities, then transition to Phase 3."""
            try:
                self.instance.room_capacities = []  # Clear existing room capacities
                # Collect and validate capacities from user inputs
                for entry in self.room_capacity_entries:
                    capacity = int(entry.get())
                    self.instance.room_capacities.append(capacity)
                # Proceed to Phase 3: Assigning students to exams
                self.create_phase3_widgets()
            except ValueError:
                # Show an error message if any capacity input is invalid
                messagebox.showerror("Invalid input", "Please enter valid integers.")

        def create_phase3_widgets(self):
            """Create and display widgets for Phase 3: Assigning students to exams."""
            self.clear_widgets()  # Clear any existing widgets from Phase 2
            self.container.grid_rowconfigure(0, weight=1)
            self.container.grid_columnconfigure(0, weight=1)

            # Create a frame for Phase 3
            phase_frame = tk.Frame(self.container)
            phase_frame.grid(row=0, column=0, sticky="nsew")
            phase_frame.grid_rowconfigure(0, weight=1)
            phase_frame.grid_columnconfigure(0, weight=1)

            # Title for Phase 3
            phase_label = tk.Label(phase_frame, text="Phase 3: Assign Students to Exams", font=("Arial", 14))
            phase_label.pack(pady=10)

            # Add a scrollable canvas for the student-exam assignment grid
            canvas = tk.Canvas(phase_frame)
            canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

            # Add a scrollbar linked to the canvas
            scrollbar = tk.Scrollbar(phase_frame, command=canvas.yview)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            canvas.configure(yscrollcommand=scrollbar.set)

            # Create a frame inside the canvas for the assignment grid
            frame = tk.Frame(canvas)
            canvas.create_window((0, 0), window=frame, anchor='nw')

            # Initialize dictionary to store checkbutton variables for assignments
            self.checkbutton_vars = {}
            for s in range(self.instance.number_of_students):
                self.checkbutton_vars[s] = {}

            # Header row for exams
            tk.Label(frame, text="Student/Exam").grid(row=0, column=0, sticky='w')  # Label for the first column
            for e in range(self.instance.number_of_exams):
                # Labels for each exam column
                tk.Label(frame, text=f"Exam {e}").grid(row=0, column=e + 1)

            # Rows for each student with checkboxes for exams
            for s in range(self.instance.number_of_students):
                # Label for each student row
                tk.Label(frame, text=f"Student {s}").grid(row=s + 1, column=0, sticky='w')
                for e in range(self.instance.number_of_exams):
                    # Create a checkbox for each student-exam combination
                    var = tk.IntVar()  # Variable to store checkbox state
                    self.checkbutton_vars[s][e] = var
                    tk.Checkbutton(frame, variable=var).grid(row=s + 1, column=e + 1)

            # Button to solve the problem after assignments are made
            next_button = tk.Button(phase_frame, text="Solve", command=self.phase3_next)
            next_button.pack(pady=10)

        def phase3_next(self):
            """Collect student-exam assignments and solve the problem."""
            self.instance.exams_to_students = []  # Reset existing student-exam mappings
            self.instance.student_exam_capacity = [0] * self.instance.number_of_exams  # Reset exam capacities
            # Loop through all students and exams to collect assignments
            for s in range(self.instance.number_of_students):
                for e in range(self.instance.number_of_exams):
                    if self.checkbutton_vars[s][e].get() == 1:  # Check if the checkbox is selected
                        self.instance.exams_to_students.append((e, s))  # Add the mapping
                        self.instance.student_exam_capacity[e] += 1  # Increment the count for this exam
            # Proceed to solving the scheduling problem
            self.phase4_solve()

        def phase4_solve(self):
            """Solve the scheduling problem and display the solutions."""
            # Clear any existing widgets from previous phases
            self.clear_widgets()
            
            # Create a new frame for displaying the solution phase
            phase_frame = tk.Frame(self.container)
            phase_frame.pack(pady=10)
            
            # Title label for the solution phase
            phase_label = tk.Label(phase_frame, text="Phase 4: Solution", font=("Arial", 16, "bold"))
            phase_label.pack()
            self.widgets['phase_label'] = phase_label

            # Retrieve the user selection for finding all solutions
            find_all_solutions = self.find_all_var.get()

            # Call the solver with the current instance and selected option
            solutions, solve_time, output_text = solve(self.instance, find_all_solutions=find_all_solutions)

            # Display the time taken and the number of solutions found
            time_label = tk.Label(
                phase_frame, 
                text=f"Solved in {solve_time:.3f} seconds, found {len(solutions)} solution(s)", 
                font=("Arial", 12, "italic")
            )
            time_label.pack(anchor='w', padx=10)
            self.widgets['time_label'] = time_label

            # Check if any solutions were found
            if not solutions:
                # Display a message if no solutions are found
                result_label = tk.Label(
                    phase_frame, 
                    text="No solution found.", 
                    font=("Arial", 14, "bold")
                )
                result_label.pack(pady=10)
                self.widgets['result_label'] = result_label
            else:
                # Store the solutions and initialize the current solution index
                self.solutions = solutions
                self.current_solution_index = 0

                # Create a dropdown menu for selecting a solution
                selection_frame = tk.Frame(phase_frame)
                selection_frame.pack(pady=10)

                # Label for the solution selector
                solution_label = tk.Label(selection_frame, text="Select Solution:")
                solution_label.pack(side=tk.LEFT)

                # Generate solution numbers for the dropdown menu
                solution_numbers = [f"Solution {i+1}" for i in range(len(solutions))]
                self.solution_var = tk.StringVar()
                self.solution_var.set(solution_numbers[0])  # Default to the first solution

                # Dropdown menu for solution selection
                solution_menu = ttk.Combobox(
                    selection_frame, 
                    textvariable=self.solution_var, 
                    values=solution_numbers, 
                    state="readonly"
                )
                solution_menu.pack(side=tk.LEFT)
                solution_menu.bind("<<ComboboxSelected>>", self.update_solution_display)

                # Display the first solution by default
                self.display_solution(solutions[0])

        def update_solution_display(self, event):
            """Update the display when a different solution is selected from the dropdown."""
            # Retrieve the selected solution index from the dropdown
            selected = self.solution_var.get()
            index = int(selected.split()[1]) - 1  # Convert "Solution X" to index X-1
            self.current_solution_index = index

            # Clear previous solution widgets
            self.clear_timetable_widgets()

            # Display the newly selected solution
            self.display_solution(self.solutions[index])

        def clear_timetable_widgets(self):
            """Remove any widgets associated with the displayed solution."""
            if 'notebook' in self.widgets:
                # Destroy the notebook widget containing the timetables
                self.widgets['notebook'].destroy()
                # Remove other associated widgets if necessary

        def display_solution(self, result):
            """
            Display the solution using a tabbed notebook interface.
            Each tab represents a different perspective of the timetable (e.g., by student, exam, room, or day).
            """
            # Create a notebook to hold all timetable views
            notebook = ttk.Notebook(self.container)
            notebook.pack(fill=tk.BOTH, expand=True, pady=10)
            self.widgets['notebook'] = notebook

            # Student Timetables Tab
            student_frame = tk.Frame(notebook)
            notebook.add(student_frame, text="Student Timetables")
            student_notebook = ttk.Notebook(student_frame)
            student_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            # Populate student-specific timetables
            for student in range(self.instance.number_of_students):
                frame = tk.Frame(student_notebook)
                student_notebook.add(frame, text=f"Student {student}")

                # Create a treeview for displaying student's timetable
                tree = ttk.Treeview(frame)
                tree['columns'] = ('Exam', 'Room', 'Slot', 'Day')
                tree.column("#0", width=0, stretch=tk.NO)  # Hide the default empty column
                tree.column("Exam", anchor=tk.CENTER, width=80)
                tree.column("Room", anchor=tk.CENTER, width=80)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Day", anchor=tk.CENTER, width=80)

                # Set up column headers
                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Exam", text="Exam", anchor=tk.CENTER)
                tree.heading("Room", text="Room", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Day", text="Day", anchor=tk.CENTER)

                # Add rows for exams assigned to this student
                for exam, assigned_student in self.instance.exams_to_students:
                    if assigned_student == student:
                        exam_info = next((r for r in result if r['Exam'] == exam), None)
                        if exam_info:
                            tree.insert(
                                parent='', index='end', text='',
                                values=(exam, exam_info['Room'], exam_info['Slot'], exam_info['Day'])
                            )

                # Pack the treeview into the frame
                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'student_{student}_tree'] = tree

            # Exam Timetables Tab
            exam_frame = tk.Frame(notebook)
            notebook.add(exam_frame, text="Exam Timetables")
            exam_notebook = ttk.Notebook(exam_frame)
            exam_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            # Populate exam-specific timetables
            for exam in range(self.instance.number_of_exams):
                frame = tk.Frame(exam_notebook)
                exam_notebook.add(frame, text=f"Exam {exam}")

                # Create a treeview for displaying exam details
                tree = ttk.Treeview(frame)
                tree['columns'] = ('Student', 'Room', 'Slot', 'Day')
                tree.column("#0", width=0, stretch=tk.NO)  # Hide the default empty column
                tree.column("Student", anchor=tk.CENTER, width=80)
                tree.column("Room", anchor=tk.CENTER, width=80)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Day", anchor=tk.CENTER, width=80)

                # Set up column headers
                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Student", text="Student", anchor=tk.CENTER)
                tree.heading("Room", text="Room", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Day", text="Day", anchor=tk.CENTER)

                # Add rows for students assigned to this exam
                exam_info = next((r for r in result if r['Exam'] == exam), None)
                if exam_info:
                    for exam_student, student in self.instance.exams_to_students:
                        if exam_student == exam:
                            tree.insert(
                                parent='', index='end', text='',
                                values=(student, exam_info['Room'], exam_info['Slot'], exam_info['Day'])
                            )

                # Pack the treeview into the frame
                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'exam_{exam}_tree'] = tree

            # Room Timetables Tab
            room_frame = tk.Frame(notebook)
            notebook.add(room_frame, text="Room Timetables")
            room_notebook = ttk.Notebook(room_frame)
            room_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            # Populate room-specific timetables
            for room in range(self.instance.number_of_rooms):
                frame = tk.Frame(room_notebook)
                room_notebook.add(frame, text=f"Room {room}")

                # Create a treeview for displaying room schedules
                tree = ttk.Treeview(frame)
                tree['columns'] = ('Exam', 'Slot', 'Day')
                tree.column("#0", width=0, stretch=tk.NO)  # Hide the default empty column
                tree.column("Exam", anchor=tk.CENTER, width=80)
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Day", anchor=tk.CENTER, width=80)

                # Set up column headers
                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Exam", text="Exam", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Day", text="Day", anchor=tk.CENTER)

                # Add rows for exams scheduled in this room
                for res in result:
                    if res['Room'] == room:
                        tree.insert(
                            parent='', index='end', text='',
                            values=(res['Exam'], res['Slot'], res['Day'])
                        )

                # Pack the treeview into the frame
                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'room_{room}_tree'] = tree

            # Day Timetables Tab
            day_frame = tk.Frame(notebook)
            notebook.add(day_frame, text="Day Timetables")
            day_notebook = ttk.Notebook(day_frame)
            day_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            # Populate day-specific timetables
            for day in range(self.instance.total_exam_days):
                frame = tk.Frame(day_notebook)
                day_notebook.add(frame, text=f"Day {day}")

                # Create a treeview for displaying daily schedules
                tree = ttk.Treeview(frame)
                tree['columns'] = ('Slot', 'Exam', 'Room')
                tree.column("#0", width=0, stretch=tk.NO)  # Hide the default empty column
                tree.column("Slot", anchor=tk.CENTER, width=80)
                tree.column("Exam", anchor=tk.CENTER, width=80)
                tree.column("Room", anchor=tk.CENTER, width=80)

                # Set up column headers
                tree.heading("#0", text="", anchor=tk.CENTER)
                tree.heading("Slot", text="Slot", anchor=tk.CENTER)
                tree.heading("Exam", text="Exam", anchor=tk.CENTER)
                tree.heading("Room", text="Room", anchor=tk.CENTER)

                # Add rows for exams scheduled on this day, sorted by slots
                day_slots = sorted([res for res in result if res['Day'] == day], key=lambda r: r['Slot'])
                for res in day_slots:
                    tree.insert(
                        parent='', index='end', text='',
                        values=(res['Slot'], res['Exam'], res['Room'])
                    )

                # Pack the treeview into the frame
                tree.pack(fill=tk.BOTH, expand=True)
                self.widgets[f'day_{day}_tree'] = tree

    app = App()
    app.mainloop()

if __name__ == "__main__":
    # Setup argument parser for command-line options
    parser = argparse.ArgumentParser(description='Exam Scheduler')
    parser.add_argument('--gui', action='store_true', help='Run with GUI')  # Option to enable the GUI
    args = parser.parse_args()

    if args.gui:
        # If the GUI option is enabled, launch the GUI interface
        run_gui()
    else:
        # Non-GUI mode: List and process test files

        # Define the directory containing test instance files
        tests_dir = Path("test_instances")
        # Collect all `.txt` files in the directory
        test_files = [file for file in tests_dir.iterdir() if file.is_file() and file.suffix == '.txt']

        # Display the list of available test files
        print("Available test files:")
        for idx, test_file in enumerate(test_files):
            print(f"{idx+1}. {test_file.name}")  # Print the index and file name for user selection

        # Ask the user to select a file by entering its corresponding number
        try:
            file_choice = int(input("Enter the number of the file you want to execute: "))

            # Check if the choice is valid
            if file_choice < 1 or file_choice > len(test_files):
                print("Invalid choice")  # Display an error message for invalid input
                sys.exit(1)  # Exit the program
        except ValueError:
            print("Invalid input. Please enter a valid number.")
            sys.exit(1)

        # Get the selected test file
        selected_file = test_files[file_choice - 1]

        # Read the instance data from the selected file
        instance = read_file(str(selected_file))

        # Ask the user if they want to print all solutions or just the first one
        print_all = input("Do you want to print all solutions? (yes/no): ").strip().lower() == 'yes'

        # Solve the problem using the selected instance
        solutions, solve_time, output_text = solve(instance, find_all_solutions=print_all)

        # Display the time taken to solve and the number of solutions found
        print(f"Solved in {solve_time:.3f} seconds, found {len(solutions)} solution(s)")

        if print_all:
            # If the user chose to print all solutions, display them in batches of 100
            batch_size = 100  # Define batch size for displaying solutions
            total_solutions = len(solutions)
            current_index = 0

            while current_index < total_solutions:
                # Calculate the range of solutions to display in the current batch
                end_index = min(current_index + batch_size, total_solutions)
                print(f"Printing solutions {current_index + 1} to {end_index}:")

                # Print solutions in the current batch
                for i in range(current_index, end_index):
                    print(f"Solution {i+1}:")
                    for res_dict in solutions[i]:
                        print(f"   Exam: {res_dict['Exam']}  Room: {res_dict['Room']}  Slot: {res_dict['Slot']}  Day: {res_dict['Day']}")
                    print("――――――――――――――――――――――――")  # Separator for better readability

                # Move to the next batch
                current_index += batch_size

                # If there are more solutions, ask the user if they want to continue
                if current_index < total_solutions:
                    more = input("Do you want to see the next batch of 100 solutions? (yes/no): ").strip().lower()
                    if more != 'yes':  # Exit if the user doesn't want to see more solutions
                        break
        else:
            # If the user chose not to print all solutions, display only the first solution
            if solutions:
                print("First solution:")
                for res_dict in solutions[0]:
                    print(f"   Exam: {res_dict['Exam']}  Room: {res_dict['Room']}  Slot: {res_dict['Slot']}  Day: {res_dict['Day']}")
            else:
                # If no solutions were found, inform the user
                print("No solutions found.")
