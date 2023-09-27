import z3
from z3 import *

# gate = Array('gate', IntSort(), IntSort())

# TODO: THIS IS THE OTHER WAY AROUND
# airplane is gate, gate is airplane


# Using arrays
# 000001000
# means the gate has airplane number 6 at it
# 010000000
# means the gate has airplane number 2 at it

# the same airplane cant be at two gates: no 2 1 on the same column
# the same gate can not have two airplanes: no 2 1s on the same row



# x_{i,j} = 1 if plane i park at stand j

from z3 import *

# Define the problem
num_planes = 3
num_gates = 3

# Initialize Z3 variables
X = [[Bool(f'X_{i}_{j}') for j in range(num_gates)] for i in range(num_planes)]
# pretty print X
print("X matrix:")
for i, row in enumerate(X):
    print(f"Plane {i}: {row}")

# Create a solver instance
s = Solver()

# Add constraints that each airplane must be at a single position
for i in range(num_planes):
    s.add(Sum([If(X[i][j], 1, 0) for j in range(num_gates)]) == 1)

# Add constraints that each position must have at most one airplane
for j in range(num_gates):
    s.add(Sum([If(X[i][j], 1, 0) for i in range(num_planes)]) <= 1)

# Check if the constraints are satisfied
if s.check() == sat:
    m = s.model()
    res = [[m.evaluate(X[i][j]) for j in range(num_gates)] for i in range(num_planes)]
    print(res)
    # pretty print
    for i, plane_res in enumerate(res):
        print(f"Airplane {i} assignment:")
        for j, gate in enumerate(plane_res):
            if gate:
                print(f"Gate {j}")
else:
    print('The constraints cannot be satisfied')
