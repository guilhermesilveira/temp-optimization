from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import LinearExpr

# ADDING TIME!!!!
# each gate now has time
# time 0, 1, 2 (int) => airplane is there or not (Int, 0 or 1)


my_vars = []

# temporary help, not to be used in production
def new_bool(name):
    v = model.NewBoolVar(name)
    my_vars.append(v)
    return v


# 5 gates, 5 planes
# one gate is never used
# 00000001000000
# 00001000000000
# 00000001000100
# 00000000000000
# 01000000000000

# Define the problem
num_planes = 3
num_gates = 3
num_times = 5  # Total number of time moments

model = cp_model.CpModel()
solver = cp_model.CpSolver()


def solve(solver, model):
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        # for each plane, ƒind the 1 in the row and print it
        for i in range(num_planes):
            found = False
            for j in range(num_gates):
                # loops for k
                result = ""
                for k in range(num_times):
                    value = solver.Value(X[i][j][k])
                    result += str(value)
                # if result contains 1
                if "1" in result:
                    print(f"Plane {i} at gate {j} is {result}")
                    found = True
            if not found:
                print(f"No solution found for plane {i}")
        for v in my_vars:
            print(f"{v} = {solver.Value(v)}")
        
        # TODO: remember to add this
        # print(f"Total cost: {solver.ObjectiveValue()}")
    else:
        print('No solution found!\n\n\n')
    print("\n\n\n")

# if airplane 4, gate 5 is:
# 00000001000000
# this means, that the airplane 4 is there at gate 5 at time 8 (1-based index)
# all other gates for airplane 4 are:
# 00000000000000

X = [[[model.NewBoolVar(f'airplane_{i}_at_gate_{j}_time_{k}')
            for k in range(num_times)]
            for j in range(num_gates)]
            for i in range(num_planes)]

# Add constraint that every airplane must be at least one gate at one moment
for i in range(num_planes):
    model.Add(sum([X[i][j][k] for j in range(num_gates) for k in range(num_times)]) >= 1)

solve(solver, model)


# Add constraint that no two airplanes can be at the same time at the same gate
for j in range(num_gates):
    for k in range(num_times):
        model.Add(sum([X[i][j][k] for i in range(num_planes)]) <= 1)
#         model.AddAtMostOne([X[i][j][k] for i in range(num_planes)])

solve(solver, model)

# Plane 0 at gate 1 is 00011
# Plane 0 at gate 2 is 11110
# Plane 1 at gate 0 is 11111
# Plane 1 at gate 1 is 11100
# Plane 2 at gate 2 is 00001
# if one gate, no other gates

# Add constraint that if a plane is at one gate, it is not in any other gates
for i in range(num_planes):
#     # for each gate, if it is there, it can not be on other gates
    for j in range(num_gates):

        # TODO: call it X again, it is at this specific gate (at any point in time)
        is_this_gate = new_bool(f'plane_{i}_gate_{j}_sum')
        model.Add(LinearExpr.Sum([X[i][j][k] for k in range(num_times)]) > 0).OnlyEnforceIf(is_this_gate);
        model.Add(LinearExpr.Sum([X[i][j][k] for k in range(num_times)]) == 0).OnlyEnforceIf(is_this_gate.Not());

        # X_i_j => !X_i_all_other_j
        # loop for each other gate and add an implication
        # programmatic

        # or...
        # mathematical
        is_in_any_other_gate = new_bool(f'plane_{i}_gate_not_{j}_sum')
        model.Add(LinearExpr.Sum([X[i][not_j][k] for not_j in range(num_gates) if not_j != j for k in range(num_times)]) == 0).OnlyEnforceIf(is_in_any_other_gate.Not())
        model.Add(LinearExpr.Sum([X[i][not_j][k] for not_j in range(num_gates) if not_j != j for k in range(num_times)]) > 0).OnlyEnforceIf(is_in_any_other_gate)

        model.AddImplication(is_this_gate, is_in_any_other_gate.Not())


solve(solver, model)


# Add constraint that if an airplane is at one moment, it must only be at consecutive moments at that gate
# for i in range(num_planes):
#     for j in range(num_gates):
#         for k in range(num_times):
#             if k < num_times - 1:
#                 s.add(Implies(And(X[i][j][k], Not(X[i][j][k+1])), 
#                               And([Not(X[i][j][k+t]) for t in range(2, num_times-k)])))
#             if k > 0:
#                 s.add(Implies(And(X[i][j][k], Not(X[i][j][k-1])), 
#                               And([Not(X[i][j][k-t]) for t in range(1, k+1)])))
