from z3 import *
import z3

class Aviao:
  def __init__(self, k, grande, schengen=True):
    self.k = k
    self.grande = grande
    self.schengen = schengen

class Gate:
  def __init__(self, k, grande, prefered_non_schengen=False):
    self.k = k
    self.grande = grande
    self.variavel = z3.Int(f'gate_{k}')
    self.vizinhos = []
    self.prefered_non_schengen = prefered_non_schengen

  def ser_aviao_grande(self):
    return z3.Or([self.variavel == aviao.k for aviao in avioes_grandes])

  def __str__(self):
    vizinho_str = ",".join([str(v.k) for v in self.vizinhos])
    return f"[Gate #{self.k} viz:{vizinho_str}]"

  def __repr__(self):
    vizinho_str = ",".join([str(v.k) for v in self.vizinhos])
    return f"[Gate #{self.k} viz:{vizinho_str}]"


def adjacente(origem_k, adjs):
  origem = gates[origem_k - 1]
  for vizinho_k in adjs:
    vizinho = gates[vizinho_k - 1]
    origem.vizinhos.append(vizinho)


avioes = [Aviao(0, False),
          Aviao(1, True),
          Aviao(2, False),
          Aviao(3, False),
          Aviao(4, True)]
gates = [Gate(1, False),
         Gate(2, False),
         Gate(3, True),
         Gate(4, True),
         Gate(5, False, True),
         Gate(6, False, True),
         Gate(7, True)]

adjacente(3, [2, 4])

gates_variaveis = [g.variavel for g in gates]
print(gates[2].vizinhos, gates[3].vizinhos)


avioes_pequenos = [a for a in avioes if not a.grande]
avioes_grandes = [a for a in avioes if a.grande]

def one_of(v, avioes):
  return z3.Or([v == aviao.k for aviao in avioes])


def limita_tamanho_de_avioes(s):
  for g in gates:
    if g.grande:
      s.add(one_of(g.variavel, avioes))
    else:
      s.add(one_of(g.variavel, avioes_pequenos))
def limita_avioes_distintos(s):
  # o problema eh que precisamos do if not 0
  # s.add(z3.Distinct(gates_variaveis))
  # IfNot0 => Distinct, tem como otimizar????

  for aviao in avioes[1:]:
    so_um = [g == aviao.k for g in gates_variaveis]
  #   # AtMost+AtLeast = ???
    c = z3.AtMost(*so_um, 1)
    c = z3.AtLeast(*so_um, 1)
    s.add(c)



def limita_vizinhos(s):
  for gate in gates:
    if not gate.grande:
      continue
    for vizinho in gate.vizinhos:
      if vizinho.grande:
        print(f"vizinhos grandes!!! {gate.k} {vizinho.k}")
        # se o aviao é grande aqui, não pode ser grande lá

        regra = z3.Not(z3.And(gate.ser_aviao_grande(), vizinho.ser_aviao_grande()))
        s.add(regra)



s = z3.Solver()

limita_tamanho_de_avioes(s)
limita_avioes_distintos(s)
limita_vizinhos(s)

s.check()

print(s.model())