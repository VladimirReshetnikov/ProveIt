#!/usr/bin/env python3
"""Split the reviewed draft without changing any declaration or proof body."""
from pathlib import Path

here = Path(__file__).resolve().parent
src = (here / "Current14Carrier65DAG.lean").read_text()
cut = src.index('/-- This is the essential bridge')
ending = '\nend DiophantineConsistency.Current14Carrier65DAG\n'
assert src.endswith(ending)
core = src[:cut].replace('import DiophantineConsistency.Carrier65\n', '', 1)
core += ending
core += '\n#print axioms DiophantineConsistency.Current14Carrier65DAG.topological\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.operation_count\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.addition_count\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.subtraction_count\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.multiplication_count\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.live_operation_count\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.all_inputs\n'
core += '#print axioms DiophantineConsistency.Current14Carrier65DAG.all_ports\n'
value = ('import DiophantineConsistency.Current14Carrier65DAGCore\n'
         'import DiophantineConsistency.Carrier65\n\n'
         'namespace DiophantineConsistency.Current14Carrier65DAG\n'
         'open ArithmeticDAG\n\n' + src[cut:] +
         '\n#print axioms DiophantineConsistency.Current14Carrier65DAG.value_eq_carrier\n')
out = here.parent / 'current14-carrier65-dag-check' / 'src' / 'DiophantineConsistency'
out.mkdir(parents=True, exist_ok=True)
(out / 'Current14Carrier65DAGCore.lean').write_text(core)
(out / 'Current14Carrier65DAGValue.lean').write_text(value)
