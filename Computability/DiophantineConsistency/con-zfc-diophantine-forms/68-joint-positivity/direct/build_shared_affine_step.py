#!/usr/bin/env python3
"""Compose a pinned authored branch-shared Horn source with affine flow."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
H=json.loads((R/'horn_shared_source.json').read_text())
def row(*terms):return [{'coefficient':c,'monomial':list(m)} for c,m in terms]
extra=[row((1,('Sp',)),(1,('Sp','v','M0')),(1,('Sp','v')),(-1,('S',)),(-1,('S','p','M0')),(-1,('S','p')),(-1,('S','q','M0')),(-1,('S','q')),(-1,('S','p','q','M0','M0')),(-2,('S','p','q','M0')),(-1,('S','p','q')))]
for a,b in [('p','dp'),('q','dq'),('v','dv')]:extra.append(row((1,(a,)),(1,(b,)),(-1,('m',))))
w=['p','q','v']+H['base_witnesses']+[f'q{i}' for i in range(H['common_wire_count'])]+['dp','dq','dv']
obj={'meaning':'local branch-shared affine accumulator polynomial, not a completed consistency equation','domain':'natural numbers','exposed_coordinates':['S','Sp','m','M0'],'witnesses':w,'witness_count':len(w),'horn_source':H,'extra_residuals':extra,'polynomial':'product of all horn branch sums of squares PLUS the sum of squares of extra_residuals','exact_degree':max(H['degree'],10),'status':'source arithmetic; global constructor uncompiled'}
(R/'affine_shared_step.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'local_witness_count':len(w),'local_degree':obj['exact_degree']},indent=2))
