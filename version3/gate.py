
import z3
from z3 import *

class Gate:
  def __init__(self, k, grande, prefered_non_schengen=False):
    self.k = k
    self.grande = grande
    self.variavel = z3.Int(f'gate_{k}')
    self.vizinhos = []
    self.prefered_non_schengen = prefered_non_schengen

  def __str__(self):
    vizinho_str = ",".join([str(v.k) for v in self.vizinhos])
    return f"[Gate #{self.k} viz:{vizinho_str}]"

  def __repr__(self):
    vizinho_str = ",".join([str(v.k) for v in self.vizinhos])
    return f"[Gate #{self.k} viz:{vizinho_str}]"
