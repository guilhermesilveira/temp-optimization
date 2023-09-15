from ortools.linear_solver import pywraplp

# Create the solver.
solver = pywraplp.Solver.CreateSolver('SAT')

# Check if the solver is available.
if not solver:
    print('Solver not available.')
    exit()

# Declare integer variables with domain [1, 3].
stand_1 = solver.IntVar(1.0, 3.0, 'stand_1')
stand_2 = solver.IntVar(1.0, 3.0, 'stand_2')

# Use a large M for the big-M method
M = 10

# Helper binary variables for the inequality.
b1 = solver.BoolVar('b1')
b2 = solver.BoolVar('b2')
b3 = solver.BoolVar('b3')

# Constraints to ensure stand_1 is not equal to stand_2.
solver.Add(stand_1 - stand_2 >= 1 - M * b1)
solver.Add(stand_1 - stand_2 <= M * b1 - 1)

solver.Add(stand_1 - stand_2 >= 2 - M * b2)
solver.Add(stand_1 - stand_2 <= M * b2 - 2)

solver.Add(stand_1 - stand_2 >= 3 - M * b3)
solver.Add(stand_1 - stand_2 <= M * b3 - 3)

# At least one of the inequalities must hold.
solver.Add(b1 + b2 + b3 >= 1)

# Call the solver.
status = solver.Solve()

# Display the results.
if status == pywraplp.Solver.OPTIMAL:
    print('stand_1 =', stand_1.solution_value())
    print('stand_2 =', stand_2.solution_value())
else:
    print('No solution found!')
