from z3 import *


# Suppose:
# 010
# 001
# 100

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
# Because gate 1 is a disaster, so the plane with least passengers goes there
# Because gate 2 is the cheapest, the plane with most passengers goes there
# FOR THIS SCENARIO, the heuristics works, but it is not guaranteed to work for all scenarios

# Define the problem
num_planes = 3
num_gates = 3
bus_required = [0, 1, 0]  # Define which gates require buses

# Initialize Z3 variables
X = [[Bool(f'X_p={i}_g={j}')
        for j in range(num_gates)]
        for i in range(num_planes)]
# pretty print X
print("X matrix:")
for i, row in enumerate(X):
    print(f"Plane {i}: {row}")

# Number of passengers and distance from gate to delivery for each plane
num_passengers = [100, 150, 200]  # Number of passengers per flight
distances = [10, 200, 20]  # Distances from each gate to the delivery point

# Cost matrices
costs = [[500 * num_passengers[i] * distances[j] if bus_required[j] else 100 * num_passengers[i] * distances[j]
          for j in range(num_gates)] for i in range(num_planes)]
# pretty print costs matrix
print("Costs matrix:")
for i, row in enumerate(costs):
    print(f"Plane {i}: {row}")

# Create an optimization instance
opt = Optimize()

# Add constraints that each airplane must be at a single position
for i in range(num_planes):
    opt.add(AtMost(*X[i], 1))
    opt.add(AtLeast(*X[i], 1))

# Add constraints that each position must have at most one airplane
for j in range(num_gates):
    opt.add(AtMost(*(X[i][j] for i in range(num_planes)), 1))

# Define the objective function (total cost)
total_cost = Sum([If(X[i][j], costs[i][j], 0)
                 for i in range(num_planes) for j in range(num_gates)])
opt.minimize(total_cost)

# Check if the constraints are satisfied
if opt.check() == sat:
    m = opt.model()
    res = [[m.evaluate(X[i][j]) for j in range(num_gates)]
           for i in range(num_planes)]
    print("Assignments:", res)
    print("Total cost:", m.evaluate(total_cost))
    # pretty print
    for i, plane_res in enumerate(res):
        print(f"Airplane {i} assignment:")
        for j, gate in enumerate(plane_res):
            if gate:
                print(f"Gate {j}")
else:
    print('The constraints cannot be satisfied')
