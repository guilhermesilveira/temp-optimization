from ortools.sat.python import cp_model


# Suppose:
# 010
# 001
# 100
# 000

# I know the number of passengers for each plane
# I know the distance from each gate to the delivery point for each plane
# I know which gates require buses
# So I know the cost:
# cost = 500 * passengers * distance if bus_required
# cost = 100 * passengers * distance otherwise
# I want to minimize the total cost


# FOR THIS EXAMPLE THE SOLUTION MUST BE
# Airplane 0 assignment:
# Gate 1
# Airplane 1 assignment:
# Gate 2
# Airplane 2 assignment:
# Gate 0
# Because gate 3 is a complete disaster, so no planes go there
# Because gate 1 is a semi-disaster, so the plane with least passengers goes there
# Because gate 2 is the cheapest, the plane with most passengers goes there
# FOR THIS SCENARIO, the heuristics works, but it is not guaranteed to work for all scenarios

# TODO all combinations in a spresheet
# 4! = 24 combinations

# but if it is a large number and other constraints becomes really hard!

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
        # TODO: remember to add this
        print(f"Total cost: {solver.ObjectiveValue()}")
    else:
        print('No solution found!\n\n\n')
    print("\n\n\n")


# Define the problem
num_planes = 3
num_gates = 3
bus_required = [0, 1, 0, 1, 0]  # Define which gates require buses

# Number of passengers and distance from gate to delivery for each plane
num_passengers = [100, 150, 200]  # Number of passengers per flight
distances = [10, 200, 20, 1000, 0]  # Distances from each gate to the delivery point

# 200 = 0 = 10 * 200 * 100 = 200.000
# 100 = 1 = 200 * 100 * 500 = 10.000.000
# 150 = 2 = 20 * 150 * 100 = 300.000
# 10.500.000

X = [[model.NewBoolVar(f'airplane_{i}_at_gate_{j}')
      for j in range(num_gates)] for i in range(num_planes)]

for i, row in enumerate(X):
    print(f"Plane {i}: {row}")
print()

# Add constraints that each airplane must be at a single position
for i in range(num_planes):
    # only works with booleans
    model.AddExactlyOne(X[i])

# Add constraints that each position must have at most one airplane
for j in range(num_gates):
    model.AddAtMostOne([X[i][j] for i in range(num_planes)])

# Cost matrices
costs = [[500 * num_passengers[i] * distances[j] if bus_required[j] else 100 * num_passengers[i] * distances[j]
          for j in range(num_gates)] for i in range(num_planes)]
# pretty print costs matrix
print("Costs matrix:")
for i, row in enumerate(costs):
    print(f"Plane {i}: {row}")

def multiply_by_array(airplanes, costs):
    # multiplies with 2 explicit for loops
    return [airplanes[i][j] * costs[i][j]
                for i in range(num_planes)
                for j in range(num_gates)]

# example 
#           [100000, 10000000, 200000, 50000000]
#           [150000, 15000000, 300000, 75000000]
#           [200000, 20000000, 400000, 100000000]
# [1 0 0 0]
# [0 1 0 0]
# [0 0 1 0]

# new!!!
model.Minimize(sum(multiply_by_array(X, costs)))

solve(solver, model)

# run with 3, with 4, with 5 where the last one is free
