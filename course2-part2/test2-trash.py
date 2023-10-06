# from z3 import *

# # WHAT IS HAPPENING ON THIS ONE???????? GUI: come back

# # Define the problem
# num_planes = 3
# num_gates = 3
# num_times = 5  # Total number of time moments

# # Initialize Z3 variables
# X = [[[Bool(f'X_{i}_{j}_{k}') for k in range(num_times)] for j in range(num_gates)] for i in range(num_planes)]

# # Create a solver instance
# s = Solver()

# # Add constraint that no two airplanes can be at the same gate at the same moment
# for j in range(num_gates):
#     for k in range(num_times):
#         s.add(AtMost(*[X[i][j][k] for i in range(num_planes)], 1))

# # Add constraint that every airplane must be at at least one gate at one moment
# for i in range(num_planes):
#     s.add(Or(*[X[i][j][k] for j in range(num_gates) for k in range(num_times)]))

# # Add constraint that if an airplane is at one moment, it must only be at consecutive moments at that gate
# for i in range(num_planes):
#     for j in range(num_gates):
#         for k in range(num_times):
#             if k < num_times - 1:
#                 s.add(Implies(And(X[i][j][k], Not(X[i][j][k+1])), 
#                               And([Not(X[i][j][k+t]) for t in range(2, num_times-k)])))
#             if k > 0:
#                 s.add(Implies(And(X[i][j][k], Not(X[i][j][k-1])), 
#                               And([Not(X[i][j][k-t]) for t in range(1, k+1)])))

# # Force every variable to be either True or False
# for i in range(num_planes):
#     for j in range(num_gates):
#         for k in range(num_times):
#             s.add(Or(X[i][j][k], Not(X[i][j][k])))

# # Check if the constraints are satisfied
# if s.check() == sat:
#     m = s.model()
#     res = [[[is_true(m.evaluate(X[i][j][k])) for k in range(num_times)] for j in range(num_gates)] for i in range(num_planes)]
    
#     # Print the results in a more readable format
#     for i, plane_res in enumerate(res):
#         print(f"Airplane {i} assignment:")
#         for k in range(num_times):
#             for j in range(num_gates):
#                 if plane_res[j][k]:
#                     print(f"  Time {k}: Gate {j}")
#     print("\n")
    
# else:
#     print('The constraints cannot be satisfied')
