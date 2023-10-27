from ortools.sat.python import cp_model

# TODO: its only one change,. ExactlyOne (so probably same video)
# now using AtMostOne and ExactlyOne

model = cp_model.CpModel()
solver = cp_model.CpSolver()


def solve(solver, model):
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        # for each plane, ƒind the 1 in the row and print it
        for i in range(num_planes):
            found = False
            for j in range(num_gates):
                value = solver.Value(X[i][j])
                if value:
                    print(f"Plane {i} at gate {j} is {value}")
                    found = True
            if not found:
                print("No solution found for plane {i}")
    else:
        print('No solution found!\n\n\n')
    print("\n\n\n")


# Define the problem
num_planes = 3
num_gates = 4

X = [[model.NewBoolVar(f'airplane_{i}_at_gate_{j}')
      for j in range(num_gates)] for i in range(num_planes)]

for i, row in enumerate(X):
    print(f"Plane {i}: {row}")
print()

# Add constraints that each airplane must be at a single position
for i in range(num_planes):
    # only works with booleans
    model.AddExactlyOne(X[i])

solve(solver, model)


# Add constraints that each position must have at most one airplane
for j in range(num_gates):
    model.AddAtMostOne([X[i][j] for i in range(num_planes)])

solve(solver, model)
