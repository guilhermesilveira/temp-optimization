# test soft

from z3 import *
import z3

# x > 5
x = z3.Int('x')
s = Optimize()
s.add([x > 5, x != 6])
s.add_soft(x > 10)
print(s.check())
print(s.model())