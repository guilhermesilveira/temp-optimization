import z3

class Aviao:
  def __init__(self, k, grande, schengen=True):
    self.k = k
    self.grande = grande
    self.schengen = schengen
    # self.variavel = z3.Int(f'aviao_{k}')

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



gates_variaveis = [g.variavel for g in gates]
print(gates[2].vizinhos, gates[3].vizinhos)

gates_v = [Int() for i in range(1, 8)]

def limita_tamanho_de_avioes(s):
    s.add(one_of(gates_v[0], avioes_pequenos))
    s.add(one_of(gates_v[1], avioes_pequenos))
    s.add(one_of(gates_v[2], avioes))
    s.add(one_of(gates_v[3], avioes))
    s.add(one_of(gates_v[4], avioes_pequenos))
    s.add(one_of(gates_v[5], avioes_pequenos))
    s.add(one_of(gates_v[6], avioes))


optim = Optimize()
