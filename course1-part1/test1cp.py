from ortools.sat.python import cp_model


# Do the entire course in google collab
# install chatgpt on collab

# Create the model.
model = cp_model.CpModel()

# Declare an integer variable. Here, we're just setting an arbitrary large range.
x = model.NewIntVar(0, 1000, 'x')

# Add the constraints.
model.Add(x > 5)
model.Add(x != 6)

# Create a solver and solve.
solver = cp_model.CpSolver()
status = solver.Solve(model)

# Display the results.
print(solver.StatusName(status))
print('x =', solver.Value(x))
