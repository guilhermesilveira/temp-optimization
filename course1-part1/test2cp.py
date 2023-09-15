from ortools.sat.python import cp_model

# Create the model.
model = cp_model.CpModel()

# Declare an integer variable.
x = model.NewIntVar(0, 1000, 'x')

# Add the hard constraints.
model.Add(x >= 7)  # Combines both constraints: x >= 6 and x >= 7.

# Model the soft constraint: x > 10
# Introduce a helper binary variable.
b = model.NewBoolVar('b')

# If b=1, then x > 10. If b=0, x can be <= 10.
model.Add(x > 10).OnlyEnforceIf(b)
model.Add(x <= 10).OnlyEnforceIf(b.Not())

# Objective: Maximize b. This encourages the solver to try to make x > 10.
model.Maximize(b)

# Create a solver and solve.
solver = cp_model.CpSolver()
status = solver.Solve(model)

# Display the results.
if status == cp_model.OPTIMAL:
    print('Objective value =', solver.ObjectiveValue())
    print('x =', solver.Value(x))
else:
    print('No solution found!')



# Choose SAT (CP-SAT):
# When dealing with highly combinatorial problems.
# If the problem has a lot of constraints that can help prune the search space effectively.
# When using global constraints or when there's a need for specialized constraint handling.
# Choose MIP:
# For linear problems or problems that can be effectively formulated as MILPs.
# If the problem is large-scale with many variables and constraints but has a predominantly linear structure


# LP vs. MILP: LPs are generally easier to solve than MILPs. While LPs can be solved in polynomial time using algorithms like Interior Point methods, MILPs are NP-hard and can be computationally challenging.

# MILP vs. SAT: Both problems are NP-hard, but they are different in nature. MILP solvers are designed to work with real and integer variables and linear constraints, while SAT solvers work with boolean variables and boolean constraints. The best solver to use depends on the problem's structure and the nature of the constraints and variables.

# LP vs. SAT: LPs have polynomial-time algorithms, while SAT is an NP-complete problem. However, modern SAT solvers can be surprisingly efficient for many practical problems due to advanced heuristics, learning techniques, and constraint propagation mechanisms.

