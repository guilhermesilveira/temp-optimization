from z3 import *

# during the recording, I will be erasing the older tests that does not
# support the new features of the model


def create_gates(gate_count):
    return [z3.Int(f'gate_{k}') for k in range(1, gate_count + 1)]


def constrain_to_planes(s, gates, plane_count):
    for gate in gates:
        s.add(z3.And(gate >= 1, gate <= plane_count))


def print_gates(s, gate_variables):
    for gate in gate_variables:
        print(gate, '=', s.model()[gate])
    for i in range(3):
        print()


def airplanes_2_gates_3():
    s = z3.Solver()
    gate_variables = create_gates(3)
    constrain_to_planes(s, gate_variables, 2)
    print(s)
    s.check()
    print_gates(s, gate_variables)


airplanes_2_gates_3()


def distinct_planes(s, gate_variables, airplane_count: int):
    # s.add(z3.Distinct(gate_variables))
    for i in range(1, airplane_count + 1):
        only_one = [g == i for g in gate_variables]
        c1 = z3.AtMost(*only_one, 1)
        c2 = z3.AtLeast(*only_one, 1)
        s.add(z3.And(c1, c2))


def constrain_to_planes(s, gates, plane_count):
    for gate in gates:
        s.add(z3.And(gate >= 0, gate <= plane_count))


def airplanes_2_gates_3_distinct_planes():
    s = z3.Solver()
    airplane_count = 2
    gate_variables = create_gates(3)
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    s.check()
    print_gates(s, gate_variables)


airplanes_2_gates_3_distinct_planes()


class Gate:
    def __init__(self, large):
        self.large = large


class Airplane:
    def __init__(self, k, large):
        self.k = k
        self.large = large


def limit_gate_by_plane_size(s, gate_variables, gates, airplanes):
    for gate, g in zip(gates, gate_variables):
        if not gate.large:
            s.add(
                z3.And([g != airplane.k for airplane in airplanes if airplane.large]))


def airplanes_2_gates_3_distinct_planes_size():
    s = z3.Solver()
    airplanes = [Airplane(1, True), Airplane(2, False)]
    gates = [Gate(True), Gate(False), Gate(False)]
    airplane_count = len(airplanes)

    gate_variables = create_gates(len(gates))
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    s.check()
    print_gates(s, gate_variables)


airplanes_2_gates_3_distinct_planes_size()


def airplanes_2_gates_3_distinct_planes_size_does_not_fit():
    s = z3.Solver()
    airplanes = [Airplane(1, True), Airplane(2, True)]
    gates = [Gate(True), Gate(False), Gate(False)]
    airplane_count = len(airplanes)

    gate_variables = create_gates(len(gates))
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    print(s.check() == z3.unsat)


airplanes_2_gates_3_distinct_planes_size_does_not_fit()


# ADDING NEIGHBOURS


class Gate:
    def __init__(self, k, large):
        self.large = large
        self.neighbours = []
        self.k = k
        self.variable = z3.Int(f'gate_{self.k}')


def one_of(v, airplanes):
    return z3.Or([v == airplane.k for airplane in airplanes])


def limit_neighbours(s, gates, airplanes):
    large_planes = [airplane for airplane in airplanes if airplane.large]
    for gate in gates:
        # if airplane is not large, there is no extra constraint
        if not gate.large:
            continue
        for neighbour in gate.neighbours:
            if neighbour.large:
                # you and your neighbour cannot be large at the same time
                both_large = z3.And(one_of(gate.variable, large_planes), one_of(
                    neighbour.variable, large_planes))
                s.add(z3.Not(both_large))


def airplanes_2_gates_3_distinct_planes_size_neighbours():
    s = z3.Solver()
    airplanes = [Airplane(1, True), Airplane(2, False), Airplane(3, True)]
    gates = [Gate(1, True), Gate(2, False), Gate(3, True), Gate(4, True)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    limit_neighbours(s, gates, airplanes)
    # print(s)
    s.check()
    print_gates(s, gate_variables)


airplanes_2_gates_3_distinct_planes_size_neighbours()


def airplanes_2_gates_3_distinct_planes_size_neighbours_wrong():
    s = z3.Solver()
    airplanes = [Airplane(1, True), Airplane(2, False), Airplane(3, True)]
    gates = [Gate(1, False), Gate(2, False), Gate(3, True), Gate(4, True)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    limit_neighbours(s, gates, airplanes)
    # print(s)
    print(s.check() == z3.unsat)


airplanes_2_gates_3_distinct_planes_size_neighbours_wrong()
