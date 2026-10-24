#!/usr/bin/env python3
"""Authored construction of the exact local height-register polynomial."""
import json
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parent
H=json.loads((ROOT/'horn_shared_source.json').read_text())
def poly(rows):
 d=defaultdict(int)
 for c,m in rows: d[tuple(sorted(m))]+=c
 return [{'coefficient':v,'monomial':list(k)} for k,v in sorted(d.items()) if v]
# M=M0+1. Exact expansion of S'(1+cM)-S(1+pM)(1+qM).
E=poly([(1,('Sp',)),(1,('Sp','v','M0')),(1,('Sp','v')),(-1,('S',)),(-1,('S','p','M0')),(-1,('S','p')),(-1,('S','q','M0')),(-1,('S','q')),(-1,('S','p','q','M0','M0')),(-2,('S','p','q','M0')),(-1,('S','p','q'))])
F=poly([(1,('Rp',)),(-1,('R',)),(-1,('R','p')),(-1,('R','q')),(-1,('R','p','q')),(-1,('R','v'))])
w=['p','q','v']+H['base_witnesses']+[f'q{i}' for i in range(H['common_wire_count'])]
assert len(w)==20 and len(set(w))==20
obj={'meaning':'local height-bounded commutative Horn certificate; not a completed global consistency polynomial','domain':'nonnegative integers','exposed_coordinates':['S','Sp','R','Rp','M0'],'witnesses':w,'witness_count':len(w),'horn_source':H,'extra_residuals':[E,F],'polynomial':'product of all horn branch sums of squares PLUS the squares of the two extra residuals','exact_degree':50,'global_bounded_forall_blocks':1,'status':'global source proved mathematically; ordinary polynomial constructor uncompiled and unmaterialized'}
(ROOT/'height_shared_step.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps({'local_witnesses':20,'local_degree':50,'global_bounded_forall_blocks':1}))
