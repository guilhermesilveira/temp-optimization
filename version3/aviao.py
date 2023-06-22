
import z3
from z3 import *

class Aviao:
  def __init__(self, k, grande, schengen=True):
    self.k = k
    self.grande = grande
    self.schengen = schengen
    # self.variavel = z3.Int(f'aviao_{k}')
