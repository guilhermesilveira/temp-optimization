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
        model.AddAtLeastOne([gate == i for gate in gate_variables])

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

