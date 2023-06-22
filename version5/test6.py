from z3 import *

# Define the problem
num_planes = 3
num_gates = 2
num_times = 5  # Total number of time moments

# Arrival times for each plane
arrival_times = [1, 2, 0]  # These are just example values, replace them with your actual arrival times

# Costs for each plane at each gate
costs = [[500, 1000], [600, 300], [700, 1400]]  # These are just example values, replace them with your actual costs

# Initialize Z3 variables
X = [[[Bool(f'X_{i}_{j}_{k}') for k in range(num_times)] for j in range(num_gates)] for i in range(num_planes)]
Y = [[Bool(f'Y_{i}_{j}') for j in range(num_gates)] for i in range(num_planes)]

# Create a solver instance
opt = Optimize()

# Add constraint that no two airplanes can be at the same gate at the same moment
for j in range(num_gates):
    for k in range(num_times):
        opt.add(AtMost(*[X[i][j][k] for i in range(num_planes)], 1))

# Add constraint that every airplane must be at at least one gate at one moment
for i in range(num_planes):
    opt.add(Or(*[X[i][j][k] for j in range(num_gates) for k in range(num_times)]))

# Add constraint that no airplane is at a gate before its arrival time
for i in range(num_planes):
    for j in range(num_gates):
        for k in range(arrival_times[i]):
            opt.add(Not(X[i][j][k]))

# Add constraint that once an airplane has left a gate, the gate stays unoccupied for the next time moment
for j in range(num_gates):
    for k in range(1, num_times):  # start from 1 to avoid negative index
        for i in range(num_planes):
            opt.add(Implies(
                And(
                    X[i][j][k-1],
                    Not(X[i][j][k])
                ),
                Not(Or([X[ip][j][k] for ip in range(num_planes) if ip != i]))
            ))

# Cost constraint and objective function
for i in range(num_planes):
    for j in range(num_gates):
        # Y[i][j] is true if and only if plane i is at gate j at least once
        opt.add(Y[i][j] == Or(*[X[i][j][k] for k in range(num_times)]))

# Set the optimization objective
opt.minimize(sum(Y[i][j]*costs[i][j] for i in range(num_planes) for j in range(num_gates)))

#  Check if the constraints are satisfied and the costs are minimized
if opt.check() == sat:
    m = opt.model()
    res = [[[is_true(m.evaluate(X[i][j][k])) for k in range(num_times)] for j in range(num_gates)] for i in range(num_planes)]
    costs_res = [[is_true(m.evaluate(Y[i][j])) for j in range(num_gates)] for i in range(num_planes)]

    # Print the results in a more readable format
    total_cost = sum(costs[i][j] if costs_res[i][j] else 0 for i in range(num_planes) for j in range(num_gates))
    print(f"Total cost: {total_cost}")
    
    for i, plane_res in enumerate(res):
        print(f"Airplane {i} assignment:")
        for k in range(num_times):
            for j in range(num_gates):
                if plane_res[j][k]:
                    print(f"  Time {k}: Gate {j}")
    print("\n")
else:
    print("No solution found")