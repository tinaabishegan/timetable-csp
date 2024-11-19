from z3 import *
from pathlib import Path
from timeit import default_timer as timer
import re

start = timer()

class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.total_exam_days = 0  # Total days exams can be conducted
        self.max_exams_per_room_per_day = 0  # Limit exams per room per day
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

def solve(instance):
    # Implement your solver here
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

    if s.check() == unsat:
        print('unsat')
    else:
        print('sat')
        for ex2 in range(instance.number_of_exams):
            print("   Exam: ", ex2, "  Room: ", (s.model().eval(ExamRoom(ex2))), "  Slot: ", (s.model().eval(ExamTime(ex2))), "  Day: ", (s.model().eval(ExamDay(ex2))))
        print("――――――――――――――――――――――――")

        # Print out the exam-student pairs
        print("Exam-Student Pairs:")
        for exam, student in instance.exams_to_students:
            print(f"   Exam {exam} - Student {student}")
        print("――――――――――――――――――――――――")

if __name__ == "__main__":
    # Read through all files in the folder
    tests_dir = Path("test_instances")
    for test in tests_dir.iterdir():
        if test.name != ".idea":
            instance = read_file(str(test))
            print(f"{test.name}: ", end="")
            solve(instance)

end = timer()
print('   \nElapsed time: ', int((end-start)*1000), 'milliseconds')