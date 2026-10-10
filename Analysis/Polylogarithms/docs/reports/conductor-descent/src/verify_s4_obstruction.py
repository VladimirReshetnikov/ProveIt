#!/usr/bin/env python3
"""Finite law-vocabulary obstruction, NOT a disproof of the S4 conjecture."""
import json,pathlib
import sympy as s
from s4_rows import build
root=pathlib.Path(__file__).resolve().parents[1]
variables,A,descs,row=build(5)
r=s.Matrix([row([(7,4,1,1,2),(3,4,1,1,0),(3,3,2,1,0),(9,2,3,1,0)])])
assignments={(1,4,1,0):-2,(2,3,0,1):1,(2,3,1,0):3,(2,3,1,3):-1,
             (3,2,0,1):-3,(3,2,1,0):-1,(3,2,1,3):-1,(4,1,0,1):2}
v=s.Matrix([assignments.get(tuple(x),0) for x in variables])
assert A*v==s.zeros(A.rows,1)
assert (r*v)[0]==24
assert A.rank()==20 and A.col_join(r).rank()==21
report=dict(status='exact finite presentation obstruction; conjecture not disproved',
            variable_convention='Im Li_{a,b}(i^c,i^d); conjugate pairs canonically signed',
            variables=[list(x) for x in variables],
            row_descriptions=[list(x) for x in descs],
            matrix=[[int(x) for x in A.row(i)] for i in range(A.rows)],
            target=[int(x) for x in r],witness=[int(x) for x in v],
            row_count=A.rows,column_count=A.cols,rank=20,augmented_rank=21,
            target_pairing=24,all_rows_annihilate_witness=True)
(root/'certificates/s4_obstruction.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: 96 x 24 matrix has rank 20; all rows annihilate witness; target pairing is 24.')
