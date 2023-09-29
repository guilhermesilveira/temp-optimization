
from ortools.sat.python import cp_model


# SCHENGEN

class Airplane:
    def __init__(self, k, large, schengen):
        self.k = k
        self.large = large
        self.schengen = schengen

    def __repr__(self):
        return f"Airplane({self.k}, large={self.large} schengen={self.schengen})"

    def __str__(self):
        return self.__repr__()


class Gate:
    def __init__(self, k, large, model, max_planes, schengen_only):
        self.large = large
        self.neighbours = []
        self.k = k
        # Assuming 3 as the maximum value based on the number of airplanes
        self.variable = model.NewIntVar(0, max_planes, f'gate_{self.k}')
        self.receives_large = model.NewBoolVar(f'receives_large_{self.k}')
        if not self.large:
            model.Add(self.receives_large == 0)
        self.schengen_only = schengen_only


# def distinct_planes(gate_variables, model):
    # model.AddAllDifferent(gate_variables)


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
                    f"{gate} has value {k} {airplane}")
    else:
        print('No solution found!\n\n\n')
    print("\n\n\n")


def remove_from_gate(k, gate, airplanes, model):
    # print(f"Gate {k} is small can't receive: {airplanes}")
    # for each large airplane, it can not be in this gate
    for airplane in airplanes:
        if airplane.large:
            model.Add(gate != airplane.k)


def limit_neighbours(model, gates, airplanes):
    large_planes = [airplane for airplane in airplanes if airplane.large]
    for gate in gates:
        if not gate.large:
            continue
        for neighbour in gate.neighbours:
            if neighbour.large:
                # if they have a large I can not have a large
                model.Add(gate.receives_large == 0).OnlyEnforceIf(
                    neighbour.receives_large)


def limit_gate_by_plane_size(model, gate_variables, gates, airplanes):
    large_ones = [airplane for airplane in airplanes if airplane.large]
    for gate, g in zip(gates, gate_variables):
        if gate.large:
            for airplane in large_ones:
                model.Add(g != airplane.k).OnlyEnforceIf(
                    gate.receives_large.Not())
        else:
            remove_from_gate(gate.k, g, large_ones, model)


# gates that are schengen only can only receive schengen planes
def constrain_non_schengen_ones(gates, airplanes, model):
    non_schengen_airplanes = [
        airplane for airplane in airplanes if not airplane.schengen]
    schengen_gates = [gate for gate in gates if gate.schengen_only]
    for gate in schengen_gates:
        # print("Gate", gate.k, "is schengen only")
        for airplane in non_schengen_airplanes:
            model.Add(gate.variable != airplane.k)


def schengen_only_accepted():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, False, False),
                 Airplane(2, False, True)]
    max_planes = len(airplanes)
    gates = [Gate(1, False, model, max_planes, True),
             Gate(2, False, model, max_planes, True),
             Gate(3, True, model, max_planes, True),
             Gate(4, True, model, max_planes, False),
             Gate(5, False, model, max_planes, True)]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    # distinct_planes(gate_variables, model)
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)
    limit_neighbours(model, gates, airplanes)
    constrain_non_schengen_ones(gates, airplanes, model)
    every_airplane_appears_once(gate_variables, airplane_count, model)

    solve(solver, model, gate_variables, airplanes)


schengen_only_accepted()


def schengen_only_accepted2():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, False, False),
                 Airplane(2, False, True),
                 Airplane(3, False, True),
                 Airplane(4, True, False),
                 Airplane(5, True, True)]
    max_planes = len(airplanes)
    gates = [Gate(1, False, model, max_planes, True),
             Gate(2, False, model, max_planes, False),
             Gate(3, True, model, max_planes, False),
             Gate(4, True, model, max_planes, True),
             Gate(5, False, model, max_planes, True)]
    # gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    # distinct_planes(gate_variables, model)
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)
    limit_neighbours(model, gates, airplanes)
    constrain_non_schengen_ones(gates, airplanes, model)
    every_airplane_appears_once(gate_variables, airplane_count, model)

    solve(solver, model, gate_variables, airplanes)


schengen_only_accepted2()

# better:
# we want max 0-x
# we want soft x > 10
# p_1 = 10 - x
# (if 10-x>0)


# gates which are not schengen only, prefer non-schenen airplanes
def prefer_schengen(model, gates, airplanes):
    penalties = []
    non_schengen_airplanes = [
        airplane for airplane in airplanes if not airplane.schengen]
    schengen_airplanes = [
        airplane for airplane in airplanes if airplane.schengen]
    preferred_non_schengen_gates = [
        gate for gate in gates if not gate.schengen_only]
    for gate in preferred_non_schengen_gates:
        # adds a penalty for schengen flights on this gate
        for airplane in schengen_airplanes:
            # creates a penalty the penalty uses Big-M method where M=1000
            penalty = model.NewIntVar(
                0, 1000, f'penalty_{gate.k}_{airplane.k}')
            print(f"Penalty {penalty} for gate {gate.k} and airplane {airplane.k}")
            # creates a variable for gate.variable == airplane.k
            # this is 1 if the gate is the airplane, 0 otherwise
            gate_equals_airplane = model.NewBoolVar(
                f'gate_{gate.k}_equals_airplane_{airplane.k}')
            model.Add(gate.variable == airplane.k).OnlyEnforceIf(
                gate_equals_airplane)
            model.Add(gate.variable != airplane.k).OnlyEnforceIf(
                gate_equals_airplane.Not())

            # if the gate is not the airplane, the penalty is 0
            model.Add(penalty == 0).OnlyEnforceIf(gate_equals_airplane.Not())
            # if the gate is the airplane, the penalty is 1000
            model.Add(penalty == 1000).OnlyEnforceIf(gate_equals_airplane)
            penalties.append(penalty)
    # returns all penalties
    return penalties


def solve2(solver, model, gate_variables, airplanes, penalties):
    model.Minimize(sum(penalties))
    status = solver.Solve(model)
    if status == cp_model.OPTIMAL:
        # prints the minimization of penalties
        print('Objective value =', solver.ObjectiveValue())

        for gate in gate_variables:
            k = solver.Value(gate)
            airplane = airplanes[k - 1]
            if k == 0:
                print(f"{gate} has no airplane")
            else:
                print(
                    f"{gate} has value {k} {airplane}")
    else:
        print('No solution found!\n\n\n')
    print("\n\n\n")


def schengen_preferred_with_penalty():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, False, False),
                 Airplane(2, False, True)]
    max_planes = len(airplanes)
    gates = [Gate(1, False, model, max_planes, False),
             Gate(2, False, model, max_planes, False)]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)
    limit_neighbours(model, gates, airplanes)
    constrain_non_schengen_ones(gates, airplanes, model)
    every_airplane_appears_once(gate_variables, airplane_count, model)
    penalties = prefer_schengen(model, gates, airplanes)

    solve2(solver, model, gate_variables, airplanes, penalties)


schengen_preferred_with_penalty()

def schengen_preferred_with_no_penalty():
    model = cp_model.CpModel()
    solver = cp_model.CpSolver()

    airplanes = [Airplane(1, False, False),
                 Airplane(2, False, True)]
    max_planes = len(airplanes)
    gates = [Gate(1, False, model, max_planes, True),
             Gate(2, False, model, max_planes, False)]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    limit_gate_by_plane_size(model, gate_variables, gates, airplanes)
    limit_neighbours(model, gates, airplanes)
    constrain_non_schengen_ones(gates, airplanes, model)
    every_airplane_appears_once(gate_variables, airplane_count, model)
    penalties = prefer_schengen(model, gates, airplanes)

    solve2(solver, model, gate_variables, airplanes, penalties)


schengen_preferred_with_no_penalty()
