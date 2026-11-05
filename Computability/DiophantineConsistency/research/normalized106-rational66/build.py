#!/usr/bin/env python3
"""Construct the 66-row fixed-rational-leaf 106 evaluator from frozen JSON."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'fourteen-normalized-product106/polynomial.json'
PARENT_SHA='0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1'
raw=PARENT.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PARENT_SHA:raise RuntimeError('parent hash mismatch')
parent=json.loads(raw);rows=parent['source']
start=next(i for i,r in enumerate(rows) if r[0]=='q2minus1')
end=next(i for i,r in enumerate(rows) if r[0]=='R')
expected=[['q2minus1','-','q2',1],['rproduct','*','gap','q2minus1'],
          ['qMF','*','q','MF'],['maskfactor','+','MC','qMF'],
          ['mask','*','maskfactor','J'],['R','+','rproduct','mask']]
if rows[start:end+1]!=expected:raise RuntimeError('unexpected parent rank')
tail=[['q2minus1','-','q2',1],['shifted_gap','+','gap','Urank'],
      ['rank_product','*','q2minus1','shifted_gap'],['rank_linear','*','J','Wrank'],
      ['R','+','rank_product','rank_linear']]
graph={'schema':'literal_fixed_rational_arithmetic_dag_v1',
       'name':'current2011_normalized106_rational66_evaluator',
       'parent':'../fourteen-normalized-product106/polynomial.json',
       'parent_sha256':PARENT_SHA,'source':rows[:start]+tail+rows[end+1:],
       'output':parent['output'],'witnesses':parent['witnesses'],
       'witness_domain':parent['witness_domain'],
       'integer_source_ports':['beta','K0','MC','MF'],
       'fixed_runtime_leaves':['beta','K0','Urank','Wrank'],
       'derived_rational_leaves':{'Urank':{'numerator':'MF','denominator':'beta'}},
       'derived_integer_leaves':{'Wrank':'MC-MF'},
       'coefficient_binding':parent['coefficient_binding'],
       'coefficient_binding_base':'../fourteen-normalized-product106',
       'operations':66,'operation_counts':{'*':37,'+':16,'-':13},'exact_degree':106,
       'metric':'Binary +,-,* cost one; fixed rational leaves are free. Not an integer-leaf 66 record.',
       'proof_scope':'Pointwise equal to parent after the fixed-port rational specialization; inherited zero-set and degree evidence.'}
out=HERE/'polynomial.json'
if out.exists():raise RuntimeError('refusing to overwrite existing graph')
out.write_text(json.dumps(graph,indent=2,sort_keys=True)+'\n')
print(hashlib.sha256(out.read_bytes()).hexdigest())
