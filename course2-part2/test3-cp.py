# arriving time gives grace time for free

from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import LinearExpr

# ADDING TIME!!!!
# each gate now has time
# time 0, 1, 2 (int) => airplane is there or not (Int, 0 or 1)


my_vars = []

def new_bool(name, debug=True):
    v = model.NewBoolVar(name)
    if debug:
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
# Arrival times for each plane
arrival_times = [1, 2, 0]  # These are just example values, replace them with your actual arrival times


# RECODING IMPLEMENT THIS ONE TOO
num_planes = 3
num_gates = 2
num_times = 6  # Total number of time moments
# Arrival times for each plane
arrival_times = [1, 3, 0]  # These are just example values, replace them with your actual arrival times


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


# Add constraint that no two airplanes can be at the same time at the same gate
for j in range(num_gates):
    for k in range(num_times):
        model.Add(sum([X[i][j][k] for i in range(num_planes)]) <= 1)
#         model.AddAtMostOne([X[i][j][k] for i in range(num_planes)])

# Add constraint that if a plane is at one gate, it is not in any other gates
for i in range(num_planes):
#     # for each gate, if it is there, it can not be on other gates
    for j in range(num_gates):

        is_this_gate = new_bool(f'plane_{i}_gate_{j}_sum', False)
        model.Add(LinearExpr.Sum([X[i][j][k] for k in range(num_times)]) > 0).OnlyEnforceIf(is_this_gate);
        model.Add(LinearExpr.Sum([X[i][j][k] for k in range(num_times)]) == 0).OnlyEnforceIf(is_this_gate.Not());
        
        is_in_any_other_gate = new_bool(f'plane_{i}_gate_not_{j}_sum', False)
        model.Add(LinearExpr.Sum([X[i][not_j][k] for not_j in range(num_gates) if not_j != j for k in range(num_times)]) == 0).OnlyEnforceIf(is_in_any_other_gate.Not())
        model.Add(LinearExpr.Sum([X[i][not_j][k] for not_j in range(num_gates) if not_j != j for k in range(num_times)]) > 0).OnlyEnforceIf(is_in_any_other_gate)

        model.AddImplication(is_this_gate, is_in_any_other_gate.Not())




# NEWWWWWW!
# Add constraint that each plane should appear at least 3 times
for i in range(num_planes):
    model.Add(sum([X[i][j][k] for j in range(num_gates) for k in range(num_times)]) >= 3)



# Add constraint that if an airplane is at one moment, it must only be at consecutive moments at that gate
for i in range(num_planes):
    for j in range(num_gates):
        for k in range(num_times):
            if k > 0 and k < num_times - 1:
                # new var meaning
                # plane was at k-1 and plane is not at k
                plane_situation_left = new_bool(f'plane_{i}_gate_{j}_time_{k}_situation_left', False)
                model.Add(LinearExpr.Sum([X[i][j][k-1], X[i][j][k].Not()]) == 2).OnlyEnforceIf(plane_situation_left)
                model.Add(LinearExpr.Sum([X[i][j][k-1], X[i][j][k].Not()]) != 2).OnlyEnforceIf(plane_situation_left.Not())
                # model.AddImplication(plane_situation_left, X[i][j][k+1].Not())
                # sum from all k onwards should be 0
                for t in range(k + 1, num_times):
                    model.AddImplication(plane_situation_left, X[i][j][t].Not())
            if k < num_times - 1:
                plane_situation_arriving = new_bool(f'plane_{i}_gate_{j}_time_{k}_situation_arriving', False)
                model.Add(LinearExpr.Sum([X[i][j][k+1], X[i][j][k].Not()]) == 2).OnlyEnforceIf(plane_situation_arriving)
                model.Add(LinearExpr.Sum([X[i][j][k+1], X[i][j][k].Not()]) != 2).OnlyEnforceIf(plane_situation_arriving.Not())
                # model.AddImplication(plane_situation_arriving, X[i][j][k-1].Not())
                for t in range(0, k - 1):
                    model.AddImplication(plane_situation_arriving, X[i][j][t].Not())

# 1 0 11111111 => nao acontece
#     ? 0 1
#     1 0 1 ==> ja nao deixou
    # 1001
       # 1
       #0




# Add constraint that no airplane is at a gate before its arrival time
for i in range(num_planes):
    for j in range(num_gates):
        for k in range(arrival_times[i]):
            model.Add(X[i][j][k] == 0 )


solve(solver, model)



# Add constraint that every airplane must be at least one gate at the arrival time
for i in range(num_planes):
    model.Add(sum([X[i][j][arrival_times[i]] for j in range(num_gates)]) == 1)


solve(solver, model)
