from aeroporto import Aeroporto
from aviao import Aviao
from gate import Gate

avioes = [Aviao(0, False),
          Aviao(1, True),
          Aviao(2, False),
          Aviao(3, False),
          Aviao(4, True),
          Aviao(5, False, False),
          Aviao(6, False),
          Aviao(7, False)
          ]
gates = [Gate(1, False),
         Gate(2, False),
         Gate(3, True),
         Gate(4, True),
         Gate(5, False),
         Gate(6, False, True),
         Gate(7, True)]

aer = Aeroporto(gates, avioes)
aer.add_neighboor(3, [2, 4])
aer.solve()

