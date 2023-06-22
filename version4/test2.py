from z3 import *

# Define the problem
num_planes = 3
num_gates = 3

# Initialize Z3 variables
X = [[Bool(f'X_{i}_{j}') for j in range(num_gates)] for i in range(num_planes)]

# Create a solver instance
s = Solver()

# Add constraints that each airplane must be at a single position
for i in range(num_planes):
    s.add(AtMost(*X[i], 1))
    s.add(AtLeast(*X[i], 1))

# Add constraints that each position must have at most one airplane
for j in range(num_gates):
    s.add(AtMost(*(X[i][j] for i in range(num_planes)), 1))

# Check if the constraints are satisfied
if s.check() == sat:
    m = s.model()
    res = [[m.evaluate(X[i][j]) for j in range(num_gates)] for i in range(num_planes)]
    print(res)
else:
    print('The constraints cannot be satisfied')
