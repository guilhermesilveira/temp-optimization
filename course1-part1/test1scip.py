from ortools.linear_solver import pywraplp

# Create the solver.
solver = pywraplp.Solver.CreateSolver('SAT')

# Check if the solver is available.
if not solver:
    print('Solver not available.')
    exit()

# Declare an integer variable. Here, we're just setting an arbitrary large range.
x = solver.IntVar(0.0, 1000.0, 'x')

# Add the constraints.
# solver.Add(x > 5)
solver.Add(x >= 6)
# solver.Add(x != 6)
solver.Add(x >= 7)

# SHOW THAT AI will get mixed up here... because you have many ways to model
# its different than doing a loop, you have two ways, same results
# you have two ways, different results

solver.Maximize(0 - x)

# Call the solver.
status = solver.Solve()

# Display the results.
if status == pywraplp.Solver.OPTIMAL:
    print('x =', x.solution_value())
else:
    print('No solution found!')
