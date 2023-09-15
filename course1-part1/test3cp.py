from ortools.sat.python import cp_model

# Create the model.
model = cp_model.CpModel()

# Declare integer variables with domain [1, 3].
stand_1 = model.NewIntVar(1, 3, 'stand_1')
stand_2 = model.NewIntVar(1, 3, 'stand_2')

# Add constraint that the two stands cannot have the same value.
model.Add(stand_1 != stand_2)

# Create a solver and solve.
solver = cp_model.CpSolver()
status = solver.Solve(model)

# Display the results.
if status in [cp_model.FEASIBLE, cp_model.OPTIMAL]:
    print('stand_1 =', solver.Value(stand_1))
    print('stand_2 =', solver.Value(stand_2))
else:
    print('No solution found!')
