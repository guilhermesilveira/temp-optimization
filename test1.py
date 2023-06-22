from z3 import *
import z3

# x > 5
x = z3.Int('x')
constraints = [x > 5, x != 6]
print(z3.solve(constraints))