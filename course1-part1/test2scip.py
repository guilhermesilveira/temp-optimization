from ortools.linear_solver import pywraplp

# if this is more complex, IGNORE... at least show once the BIG M

# Create the solver.
solver = pywraplp.Solver.CreateSolver('SAT')

# Check if the solver is available.
if not solver:
    print('Solver not available.')
    exit()

# Declare an integer variable.
x = solver.IntVar(0.0, 1000.0, 'x')

# Add the hard constraints.
solver.Add(x >= 6)
solver.Add(x >= 7)

# Model the soft constraint: x > 10
# Introduce a helper binary variable.
b = solver.BoolVar('b')

# If b=1, then x > 10. If b=0, x can be <= 10.
solver.Add(x <= 10 + 1000 * b)
solver.Add(x >= 11 - 1000 * (1 - b))

# Objective: Maximize b. This encourages the solver to try to make x > 10.
solver.Maximize(b)

# Call the solver.
status = solver.Solve()

# Display the results.
if status == pywraplp.Solver.OPTIMAL:
    print('Objective value =', solver.Objective().Value())
    print('x =', x.solution_value())
else:
    print('No solution found!')
