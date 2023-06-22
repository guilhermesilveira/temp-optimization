from z3 import *
import z3

# assentos

stand_1 = z3.Int('stand_1')
stand_2 = z3.Int('stand_2')
# o valor pode ser 1, 2 ou 3

s = z3.Solver()
s.add(1 <= stand_1, stand_1 <= 3)
s.add(1 <= stand_2, stand_2 <= 3)
s.add(stand_1 != stand_2)
s.check()
print(s.model())