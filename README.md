# Exam Scheduler using Z3 Solver

## Project Description

The **Exam Scheduler** is a Python application designed to generate feasible exam timetables based on a set of constraints and inputs. It leverages the power of the **Z3 Solver**, a high-performance theorem prover developed by Microsoft Research, to find solutions to complex scheduling problems efficiently.

This application can be run in two modes:

- **GUI Mode**: A user-friendly graphical interface built with Tkinter, allowing users to input data step by step and visualize the solutions interactively.
- **Non-GUI Mode**: A command-line interface where users can select predefined test instances and control the solution-finding process via prompts.

### Key Features

- **Flexible Input Methods**:
  - **GUI Mode**: Input data manually or load from a `.txt` file.
  - **Non-GUI Mode**: Select from available test instances in the `test_instances` directory.
- **Constraint Handling**:
  - No student has overlapping exams.
  - Room capacities are respected.
  - Limits on the number of exams per room per day.
- **Solution Options**:
  - Option to find all possible solutions or stop after the first feasible one.
  - Solutions displayed in batches for large result sets.
- **Detailed Solution Visualization**:
  - **GUI Mode**: Solutions displayed in tabbed notebooks categorized by students, exams, rooms, and days.
  - **Non-GUI Mode**: Solutions printed in an easy-to-read format in the terminal.


## Table of Contents

1. [Installation](#installation)
2. [Usage](#usage)
   - [GUI Mode](#gui-mode)
   - [Non-GUI Mode](#non-gui-mode)
3. [Project Structure](#project-structure)
4. [Dependencies](#dependencies)
5. [Contributing](#contributing)
6. [License](#license)

## Installation

### Prerequisites

- **Python 3.6 or higher**: Ensure Python is installed on your system.
- **Z3 Solver**: Install the Z3 Python bindings.

### Steps

1. **Clone the Repository**

   ```bash
   gh repo clone tinaabishegan/timetable-csp
   ```

2. **Install Required Python Packages**

   Install the dependencies using `pip`:

   ```bash
   pip install -r requirements.txt
   ```


3. **Verify Z3 Installation**

   Confirm that Z3 is correctly installed:

   ```bash
   python -c "import z3; print(z3.get_version())"
   ```

   This should output the version number of the Z3 Solver.

4. **Set Up Test Instances**

   Ensure the `test_instances` directory exists and contains `.txt` files with test instances. You can create your own test instances or use provided examples.

## Usage

The application supports both GUI and Non-GUI modes.

### GUI Mode

Run the application in GUI mode with:

```bash
python timetabling.py --gui
```

#### Steps in GUI Mode

1. **Phase 1: Enter Basic Information**

   - **Input Fields**:
     - **Number of students**: Total number of students.
     - **Number of exams**: Total number of exams to schedule.
     - **Number of timeslots**: Number of available timeslots per day.
     - **Number of rooms**: Total number of rooms available.
     - **Total exam days**: Number of days over which exams can be scheduled.
     - **Max exams per room per day**: Maximum number of exams that can be held in a room per day.
   - **Options**:
     - **Find all possible solutions**: Check this box if you wish to find all feasible solutions; uncheck to find only the first feasible solution.
     - **Select a `.txt` file**: Click "Select File" to load data from a text file. This will bypass manual input and proceed directly to solving.

2. **Phase 2: Enter Room Capacities**

   - Input the capacity for each room. Ensure that the capacities are sufficient to accommodate the assigned exams.

3. **Phase 3: Assign Students to Exams**

   - **Assignment Grid**: A grid where rows represent students and columns represent exams.
   - **Assigning Students**: Check the boxes corresponding to the exams each student is enrolled in.

4. **Phase 4: View Solutions**

   - **Solution Summary**: Displays the time taken to solve and the number of solutions found.
   - **Solution Selection**: If multiple solutions are found, select which one to view from a dropdown menu.
   - **Timetable Visualization**:
     - **Student Timetables**: View each student's exam schedule.
     - **Exam Timetables**: See which students are taking each exam, along with room and time details.
     - **Room Timetables**: View the schedule for each room.
     - **Day Timetables**: See all exams scheduled for each day.

#### Notes

- **Data Validation**: All inputs are validated for correctness. Ensure that you provide valid integers in all input fields.
- **Constraints**: The application enforces all defined constraints to generate feasible timetables.

### Non-GUI Mode

Run the application in Non-GUI mode with:

```bash
python timetabling.py
```

#### Steps in Non-GUI Mode

1. **Select a Test Instance**

   - The application lists all available `.txt` files in the `test_instances` directory.
   - Enter the number corresponding to the desired test file.

2. **Choose Solution Options**

   - **Print All Solutions**: When prompted, type `yes` to find and print all solutions or `no` to stop after the first solution.

3. **View Solutions**

   - **First Solution**: If you chose not to print all solutions, the first feasible solution will be displayed.
   - **All Solutions**: If you opted to print all solutions, they will be displayed in batches of 100.
     - After each batch, you will be asked if you want to view the next batch.
   - **Solution Format**:
     - Each solution lists exam assignments with details:
       - **Exam**: Exam number.
       - **Room**: Assigned room number.
       - **Slot**: Assigned timeslot.
       - **Day**: Assigned day.

#### Example Interaction

```
Available test files:
1. sat1.txt
2. sat10.txt
3. sat2.txt
Enter the number of the file you want to execute: 2
Do you want to print all solutions? (yes/no): no
Solved in 0.567 seconds, found 1 solution(s)
First solution:
   Exam: 0  Room: 2  Slot: 1  Day: 0
   Exam: 1  Room: 1  Slot: 0  Day: 0
   Exam: 2  Room: 0  Slot: 2  Day: 0
   ...
```

## Project Structure

```
exam-scheduler/
├── timetabling.py          # Main application script
├── test_instances/         # Directory containing test instance files
│   ├── sat1.txt
│   ├── sat2.txt
│   └── sat3.txt,...,sat10.txt,unsat1.txt,...,unsat10.txt
├── requirements.txt        # Python package dependencies
└── README.md               # Project documentation
```

## Dependencies

- **Python 3.6 or higher**
- **Z3 Solver** (`z3-solver` Python package)
- **Tkinter** (usually included with Python installations)
- **Argparse** (standard library module)
- **Tkinter Modules**:
  - `tkinter.ttk`
  - `tkinter.messagebox`
  - `tkinter.filedialog`
- **Additional Python Modules**:
  - `pathlib`
  - `timeit`
  - `re`
  - `sys`


## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

---

