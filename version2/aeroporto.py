import z3
from z3 import *


def _one_of(var, avioes):
    return z3.Or([var == aviao.k for aviao in avioes])


# def ser_aviao_grande(self):
# return z3.Or([self.variavel == aviao.k for aviao in avioes_grandes])


class Aeroporto:
    def __init__(self, gates, avioes):
        self.gates = gates
        self.avioes = avioes
        self.gates_variaveis = Array('Gates', IntSort(), IntSort())
        print(self.gates_variaveis)
        for i, gate in enumerate(self.gates):
            v = self.gates_variaveis[i]
            self.gates[i].variavel = v
            print(f"Created gate {i}")
        print(self.gates_variaveis)

    def _avioes_pequenos(self):
        return [a for a in self.avioes if not a.grande]

    def _avioes_grandes(self):
        return [a for a in self.avioes if a.grande]

    def add_neighboor(self, origem_k, adjs):
        origem = self.gates[origem_k - 1]
        for vizinho_k in adjs:
            vizinho = self.gates[vizinho_k - 1]
            origem.vizinhos.append(vizinho)

    def gate_ser_aviao_grande(self, gate):
        return _one_of(gate.variavel, self._avioes_grandes())

    def limita_tamanho_de_avioes(self, s):
        print("Size:")
        for g in self.gates:
            if g.grande:
                s.add(_one_of(g.variavel, self.avioes))
            else:
                s.add(_one_of(g.variavel, self._avioes_pequenos()))

    def limita_avioes_distintos(self, s):
        print("Distinct")
        # o problema eh que precisamos do if not 0
        # s.add(z3.Distinct(gates_variaveis))
        # IfNot0 => Distinct, tem como otimizar????

        for aviao in self.avioes[1:]:
            so_um = [g.variavel == aviao.k for g in self.gates]
        #   # AtMost+AtLeast = ???
            c = And(z3.AtMost(*so_um, 1), z3.AtLeast(*so_um, 1))
            s.add(c)
            # print(c)


    def limita_vizinhos(self, s):
        print("Vizinhos")
        for gate in self.gates:
            if not gate.grande:
                continue
            for vizinho in gate.vizinhos:
                if vizinho.grande:
                    print(f"vizinhos grandes!!! {gate.k} {vizinho.k}")
                    # se o aviao é grande aqui, não pode ser grande lá

                    regra = z3.Not(z3.And(
                                    self.gate_ser_aviao_grande(gate),
                                    self.gate_ser_aviao_grande(vizinho)))
                    s.add(regra)

    def prefere_schengen(self, s):
        print("Schengen")
        # Preffered
        # 1. Stands 11 and 12 for non-Schengen flights
        non_schengen_flights = [a for a in self.avioes if not a.schengen]
        preferred = [g for g in self.gates if g.prefered_non_schengen]
        for g in preferred:
            s.add_soft(_one_of(g.variavel, non_schengen_flights))
        # aviao1 nao schengen
            # prefiro que gate11 seja 1 ou gate12 seja 1
        # prefiro que gate1 a 10 NAO seja o aviao 1

    def solve(self):
        # print("Vizinhos do gate 3:", self.gates[2].vizinhos)
        # print("Vizinhos do gate 4:", self.gates[3].vizinhos)
        s = Optimize()
        print("Optimizer")
        self.limita_tamanho_de_avioes(s)
        self.limita_avioes_distintos(s)
        self.limita_vizinhos(s)
        self.prefere_schengen(s)
        print("pronto")
        # print(s)
        # print("check")
        print(s.check())
        print(s.model())
