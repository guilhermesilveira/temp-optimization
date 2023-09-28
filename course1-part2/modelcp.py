from ortools.sat.python import cp_model


def create_gates(gate_count, airplane_count, model):
    return [model.NewIntVar(1, airplane_count, f'gate_{k}') for k in range(1, gate_count + 1)]


def solve(solver, model, gate_variables):
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        for gate in gate_variables:
            print(gate, '=', solver.Value(gate))
        print("\n\n\n")
    else:
        print('No solution found!\n\n\n')


def airplanes_2_gates_3():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    gate_variables = create_gates(3, 2, model)
    solve(solver, model, gate_variables)


airplanes_2_gates_3()


def distinct_planes(gate_variables, model):
    model.AddAllDifferent(gate_variables)


def airplanes_2_gates_3_distinct_planes():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplane_count = 2
    gate_count = 3
    gate_variables = create_gates(gate_count, airplane_count, model)
    distinct_planes(gate_variables, model)
    solve(solver, model, gate_variables)


airplanes_2_gates_3_distinct_planes()


def airplanes_3_gates_2_distinct_planes():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplane_count = 3
    gate_count = 2
    gate_variables = create_gates(gate_count, airplane_count, model)
    distinct_planes(gate_variables, model)
    solve(solver, model, gate_variables)


airplanes_3_gates_2_distinct_planes()


def create_gates(gate_count, airplane_count, model):
    return [model.NewIntVar(0, airplane_count, f'gate_{k}') for k in range(1, gate_count + 1)]


airplanes_2_gates_3_distinct_planes()
airplanes_3_gates_2_distinct_planes()


def every_airplane_appears_once(gate_variables, airplane_count, model):
    for i in range(1, airplane_count + 1):
        model.Add(cp_model.Sum([gate == i for gate in gate_variables]) == 1)
        # solver.Sum([gate == i for gate in gate_variables])
        # model.Add(sum([gate == i for gate in gate_variables]) == 1)


def every_airplane_appears_once(gate_variables, airplane_count, model):
    for i in range(1, airplane_count + 1):
        expression_list = [(gate == i) for gate in gate_variables]
        model.Add(sum(expression_list) == 1)


def every_airplane_appears_once(gate_variables, airplane_count, model):
    ones = {}
    for i in range(1, airplane_count + 1):
        for j, gate in enumerate(gate_variables):
            ones[(i, j)] = model.NewBoolVar(f'airplane_{i}_at_gate_{j}')
            model.Add(gate == i).OnlyEnforceIf(ones[(i, j)])
            model.Add(gate != i).OnlyEnforceIf(ones[(i, j)].Not())

    for i in range(1, airplane_count + 1):
        model.AddExactlyOne([ones[(i, j)]
                            for j, _ in enumerate(gate_variables)])
        # model.Add(sum(ones[(i, j)] for j, _ in enumerate(gate_variables)) == 1)


def airplanes_2_gates_3_distinct_planes():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplane_count = 2
    gate_count = 3
    gate_variables = create_gates(gate_count, airplane_count, model)
    distinct_planes(gate_variables, model)
    every_airplane_appears_once(gate_variables, airplane_count, model)
    solve(solver, model, gate_variables)


airplanes_2_gates_3_distinct_planes()


def airplanes_3_gates_2_distinct_planes():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplane_count = 3
    gate_count = 2
    gate_variables = create_gates(gate_count, airplane_count, model)
    distinct_planes(gate_variables, model)
    every_airplane_appears_once(gate_variables, airplane_count, model)
    solve(solver, model, gate_variables)


airplanes_3_gates_2_distinct_planes()


class Gate:
    def __init__(self, large):
        self.large = large


class Airplane:
    def __init__(self, k, large):
        self.k = k
        self.large = large

    def __repr__(self):
        return f"Airplane({self.k}, {self.large})"

    def __str__(self):
        return f"Airplane({self.k}, {self.large})"


def my_sum(model, expressions):
    bool_vars = [model.NewBoolVar(f'b_{i}') for i, _ in enumerate(expressions)]
    for i, (expr, b_var) in enumerate(zip(expressions, bool_vars)):
        model.Add(expr).OnlyEnforceIf(b_var)
        model.Add(~expr).OnlyEnforceIf(b_var.Not())
    return sum(bool_vars)


def remove_from_gate(gate, airplanes, model):
    print(f"Gate is small can't receive: {airplanes}")
    # for each large airplane, it can not be in this gate
    for airplane in airplanes:
        if airplane.large:
            model.Add(gate != airplane.k)


def limit_gate_by_plane_size(model, gate_variables, gates, airplanes):
    large_ones = [airplane for airplane in airplanes if airplane.large]
    for gate, g in zip(gates, gate_variables):
        if not gate.large:
            remove_from_gate(g, large_ones, model)


def solve(solver, model, gate_variables, airplanes):
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        for gate in gate_variables:
            k = solver.Value(gate)
            airplane = airplanes[k - 1]
            if k == 0:
                print(f"{gate} has no airplane")
            else:
                print(
                    f"{gate} has value {k} airplane {airplane.k} with size {airplane.large}")
        print("\n\n\n")
    else:
        print('No solution found!\n\n\n')


def airplanes_2_gates_3_distinct_planes_size():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, True),
                 Airplane(2, False)]
    gates = [Gate(False),
             Gate(False),
             Gate(True)]
    airplane_count = len(airplanes)
    gate_count = len(gates)

    gate_variables = create_gates(gate_count, airplane_count, model)
    distinct_planes(gate_variables, model)
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)
    solve(solver, model, gate_variables, airplanes)


airplanes_2_gates_3_distinct_planes_size()


def airplanes_2_gates_3_distinct_planes_size_does_not_fit():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, True),
                 Airplane(2, True)]
    gates = [Gate(True),
             Gate(False),
             Gate(False)]
    airplane_count = len(airplanes)
    gate_count = len(gates)

    gate_variables = create_gates(gate_count, airplane_count, model)
    distinct_planes(gate_variables, model)
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)

    status = solver.Solve(model)
    print(status == cp_model.INFEASIBLE)
    print("\n\n\n")


airplanes_2_gates_3_distinct_planes_size_does_not_fit()


# ADDING NEIGHBOURS


class Gate:
    def __init__(self, k, large, model, max_planes):
        self.large = large
        self.neighbours = []
        self.k = k
        # Assuming 3 as the maximum value based on the number of airplanes
        self.variable = model.NewIntVar(0, max_planes, f'gate_{self.k}')
        self.receives_large = model.NewBoolVar(f'receives_large_{self.k}')
        if not self.large:
            model.Add(self.receives_large == 0)

def remove_from_gate(k, gate, airplanes, model):
    print(f"Gate {k} is small can't receive: {airplanes}")
    # for each large airplane, it can not be in this gate
    for airplane in airplanes:
        if airplane.large:
            model.Add(gate != airplane.k)

# def one_of(v, vars):
    # return [v == var.k for var in vars]


def limit_neighbours(model, gates, airplanes):
    large_planes = [airplane for airplane in airplanes if airplane.large]
    for gate in gates:
        if not gate.large:
            continue
        for neighbour in gate.neighbours:
            if neighbour.large:
                # if they have a large I can not have a large
                model.Add(gate.receives_large == 0).OnlyEnforceIf(neighbour.receives_large)


def limit_gate_by_plane_size(model, gate_variables, gates, airplanes):
    large_ones = [airplane for airplane in airplanes if airplane.large]
    for gate, g in zip(gates, gate_variables):
        if gate.large:
            for airplane in large_ones:
                model.Add(g != airplane.k).OnlyEnforceIf(gate.receives_large.Not())
        else:
            remove_from_gate(gate.k, g, large_ones, model)

def airplanes_2_gates_3_distinct_planes_size_neighbours():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, True),
                 Airplane(2, False),
                 Airplane(3, True)]
    max_planes = len(airplanes)
    gates = [Gate(1, True, model, max_planes),
             Gate(2, False, model, max_planes),
             Gate(3, True, model, max_planes),
             Gate(4, True, model, max_planes)]
    gates[2].neighbours = [gates[3]]

    gate_variables = [g.variable for g in gates]
    distinct_planes(gate_variables, model)
    limit_neighbours(model, gates, airplanes)
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)

    solve(solver, model, gate_variables, airplanes)


airplanes_2_gates_3_distinct_planes_size_neighbours()
def airplanes_2_gates_3_distinct_planes_size_neighbours_wrong():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, True),
                 Airplane(2, False),
                 Airplane(3, True)]
    max_planes = len(airplanes)
    gates = [Gate(1, False, model, max_planes),
             Gate(2, False, model, max_planes),
             Gate(3, True, model, max_planes),
             Gate(4, True, model, max_planes)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    distinct_planes(gate_variables, model)
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)
    limit_neighbours(model, gates, airplanes)

    status = solver.Solve(model)
    print(status == cp_model.INFEASIBLE)
    print("\n\n\n")

airplanes_2_gates_3_distinct_planes_size_neighbours_wrong()
