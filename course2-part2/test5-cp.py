# supports departure time and custom grace times
# this is old 6 and 7

from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import LinearExpr

# Define the problem
num_planes = 3
num_gates = 2
num_times = 5
arrival_times = [1, 2, 0]
staying_time = [2, 2, 2]

# Costs for each plane at each gate, should be calculated
# 2200
costs = [[500, 1000], [600, 300], [700, 1400]]

# 2000
arrival_times = [1, 3, 0]
costs = [[500, 1000], [600, 300], [700, 1400]]

# 2500
arrival_times = [1, 3, 0]
costs = [[500, 5000], [600, 13300], [700, 1400]]

my_vars = []

def new_bool(name, debug=True):
    v = model.NewBoolVar(name)
    if debug:
        my_vars.append(v)
    return v



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
        
        # NEW
        print(f"Total cost: {solver.ObjectiveValue()}")
    else:
        print('No solution found!\n\n\n')
    print("\n\n\n")

X = [[[model.NewBoolVar(f'airplane_{i}_at_gate_{j}_time_{k}')
            for k in range(num_times)]
            for j in range(num_gates)]
            for i in range(num_planes)]

Y = [[model.NewBoolVar(f'airplane_{i}_uses_gate_{j}')
            for j in range(num_gates)]
            for i in range(num_planes)]





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

        # Cost constraint and objective function
        # Y[i][j] is true if and only if plane i is at gate j at least once
        # is_this_gate is unneccessary too as it is Y[i][j] now
        model.AddImplication(is_this_gate, Y[i][j])
        model.AddImplication(is_this_gate.Not(), Y[i][j].Not())




# Add constraint that each plane should appear at least staying time
for i in range(num_planes):
    model.Add(sum([X[i][j][k] for j in range(num_gates) for k in range(num_times)]) == staying_time[i])



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





# Add constraint that no airplane is at a gate before its arrival time
for i in range(num_planes):
    for j in range(num_gates):
        for k in range(arrival_times[i]):
            model.Add(X[i][j][k] == 0 )




# Add constraint that every airplane must be at least one gate at the arrival time
for i in range(num_planes):
    model.Add(sum([X[i][j][arrival_times[i]] for j in range(num_gates)]) == 1)



def multiply_by_array(y, costs):
    # multiplies with 2 explicit for loops
    return [y[i][j] * costs[i][j]
                for i in range(num_planes)
                for j in range(num_gates)]

# In this case, only a single cost per complete stay
# It could be a cost per moment of stay
model.Minimize(sum(multiply_by_array(Y, costs)))
# opt.minimize(sum(Y[i][j]*costs[i][j] for i in range(num_planes) for j in range(num_gates)))


solve(solver, model)
