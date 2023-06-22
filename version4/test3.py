from z3 import *

# Define the problem
num_planes = 3
num_gates = 3
bus_required = [0, 1, 0]  # Define which gates require buses

# Initialize Z3 variables
X = [[Bool(f'X_{i}_{j}') for j in range(num_gates)] for i in range(num_planes)]

# Number of passengers and distance from gate to delivery for each plane
num_passengers = [100, 150, 200]  # Number of passengers per flight
distances = [[1, 2, 1], [2, 1, 3], [1, 3, 2]]  # Distances from each gate for each flight

# Cost matrices
costs = [[500 * num_passengers[i] * distances[i][j] if bus_required[j] else 100 * num_passengers[i] * distances[i][j]
          for j in range(num_gates)] for i in range(num_planes)]

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
total_cost = Sum([If(X[i][j], costs[i][j], 0) for i in range(num_planes) for j in range(num_gates)])
opt.minimize(total_cost)

# Check if the constraints are satisfied
if opt.check() == sat:
    m = opt.model()
    res = [[m.evaluate(X[i][j]) for j in range(num_gates)] for i in range(num_planes)]
    print("Assignments:", res)
    print("Total cost:", m.evaluate(total_cost))
else:
    print('The constraints cannot be satisfied')
