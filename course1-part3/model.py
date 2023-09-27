from z3 import *


# IF IT IS A SCHENGEN FLIGHT... IT PREFERS TO GO TO 1 to 10 (penalty to 11 and 12)
# IF IT IS A NON SCHENGEN FLIGHT.... IT MSUT BE 11 and 12
# the penalties will work as a weight if you are using multiple soft constraints (11 penalty 5, 12 penalty 10)


def constrain_to_planes(s, gates, plane_count):
    for gate in gates:
        s.add(z3.And(gate >= 1, gate <= plane_count))


def print_gates(s, gate_variables):
    for gate in gate_variables:
        print(gate, '=', s.model()[gate])
    for i in range(3):
        print()


def distinct_planes(s, gate_variables, airplane_count: int):
    # s.add(z3.Distinct(gate_variables))
    for i in range(1, airplane_count + 1):
        only_one = [g == i for g in gate_variables]
        c1 = z3.AtMost(*only_one, 1)
        c2 = z3.AtLeast(*only_one, 1)
        s.add(And(c1, c2))


def constrain_to_planes(s, gates, plane_count):
    for gate in gates:
        s.add(z3.And(gate >= 0, gate <= plane_count))


def limit_gate_by_plane_size(s, gate_variables, gates, airplanes):
    for gate, g in zip(gates, gate_variables):
        if not gate.large:
            s.add(
                z3.And([g != airplane.k for airplane in airplanes if airplane.large]))


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


# SCHENGEN AND PREFERENCES

# Non-Schengen MUST GO to 11 and 12

class Gate:
    def __init__(self, k, large, prefered_non_schengen):
        self.large = large
        self.neighbours = []
        self.k = k
        self.variable = z3.Int(f'gate_{self.k}')
        self.prefered_non_schengen = prefered_non_schengen


class Airplane:
    def __init__(self, k, large, schengen):
        self.k = k
        self.large = large
        self.schengen = schengen

def prefer_schengen(s, gates, airplanes):
    # passport control
    # 1. Stands 11 and 12 for non-Schengen flights

    non_schengen_flights = [a for a in airplanes if not a.schengen]
    preferred = [g for g in gates if g.prefered_non_schengen]
    for g in preferred:
        s.add_soft(one_of(g.variable, non_schengen_flights))

    # QUESTION: do they prefer ALSO schengen flights to the other ones?
    # if so, we need to add a constraint for that
    # other_planes = [a for a in airplanes if a.schengen]
    # other_gates = [g for g in gates if not g.prefered_non_schengen]
    # for g in other_gates:
    #     s.add_soft(one_of(g.variable, other_planes))


def test1():
    s = z3.Optimize()
    airplanes = [Airplane(1, False, True), Airplane(
        2, False, False), Airplane(3, False, False)]
    gates = [Gate(1, False, True), Gate(2, False, True),
             Gate(3, False, False), Gate(4, False, False)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    limit_neighbours(s, gates, airplanes)
    prefer_schengen(s, gates, airplanes)
    # print(s)
    s.check()
    print_gates(s, gate_variables)


test1()


def test2():
    s = z3.Optimize()
    airplanes = [Airplane(1, False, True), Airplane(
        2, False, True), Airplane(3, False, True), Airplane(4, False, True)]
    gates = [Gate(1, False, True), Gate(2, False, True),
             Gate(3, False, False), Gate(4, False, False)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    limit_neighbours(s, gates, airplanes)
    prefer_schengen(s, gates, airplanes)
    # print(s)
    s.check()
    print_gates(s, gate_variables)


test2()


def test3():
    s = z3.Optimize()
    airplanes = [Airplane(1, False, False), Airplane(
        2, False, True), Airplane(3, False, True), Airplane(4, False, True)]
    gates = [Gate(1, False, False), Gate(2, False, True),
             Gate(3, False, False), Gate(4, False, False)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    limit_neighbours(s, gates, airplanes)
    prefer_schengen(s, gates, airplanes)
    # print(s)
    s.check()
    print_gates(s, gate_variables)


test3()


def prefer_schengen(s, gates, airplanes):
    # passport control
    # 1. Stands 11 and 12 for non-Schengen flights

    non_schengen_flights = [a for a in airplanes if not a.schengen]
    preferred = [g for g in gates if g.prefered_non_schengen]
    for g in preferred:
        s.add_soft(one_of(g.variable, non_schengen_flights))

    # QUESTION: do they prefer ALSO schengen flights to the other ones?
    # if so, we need to add a constraint for that
    other_planes = [a for a in airplanes if a.schengen]
    other_gates = [g for g in gates if not g.prefered_non_schengen]
    for g in other_gates:
        s.add_soft(one_of(g.variable, other_planes))


def test4():
    s = z3.Optimize()
    airplanes = [Airplane(1, False, True)]
    gates = [Gate(1, False, True), Gate(2, False, True),
             Gate(3, False, False), Gate(4, False, True)]
    gates[2].neighbours = [gates[3]]
    airplane_count = len(airplanes)

    gate_variables = [g.variable for g in gates]
    constrain_to_planes(s, gate_variables, airplane_count)
    distinct_planes(s, gate_variables, airplane_count)
    limit_gate_by_plane_size(s, gate_variables, gates, airplanes)
    limit_neighbours(s, gates, airplanes)
    prefer_schengen(s, gates, airplanes)
    # print(s)
    s.check()
    print_gates(s, gate_variables)


test4()
