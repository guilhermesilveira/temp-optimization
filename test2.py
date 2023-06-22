# test soft

from z3 import *
import z3

# x > 5
x = z3.Int('x')
constraints = [x > 5, x != 6]
s = Optimize()
s.add(constraints)
s.add_soft(x > 10)
print(s.check())
print(s.model())