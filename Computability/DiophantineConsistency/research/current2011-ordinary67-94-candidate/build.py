#!/usr/bin/env python3
"""Build current-port 67/94 candidate, preserving the authenticated 51-row prefix."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
p=TASK/'research/fourteen-nonzero-spheres/polynomial71.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2': raise RuntimeError('parent hash')
g=json.loads(raw);prefix=g['source'][:51]
if prefix[-1]!=['V','-','f2inner','c']:raise RuntimeError('prefix mismatch')
tail=[['I','*','i','c2'],['I2','*','I','I'],['f2m1','-','f2',1],['Aaux','*','Delta','f2m1'],
 ['V2','*','V','V'],['y2','*','y','y'],['aux_gap','-','V2','y2'],['aux_term','*','Aaux','aux_gap'],
 ['Na','+','aux_term','y2'],['strong_residual','-','I2','Aaux'],['Ns','+','strong_residual',1],
 ['prod0','*','N0','N1'],['prod1','*','prod0','Na'],['prod2','*','prod1','Nt'],
 ['prod3','*','prod2','Ns'],['polynomial','-','prod3',1]]
out={'schema':'literal_integer_arithmetic_dag_v1','name':'current2011_ordinary67_degree94_candidate',
 'witness_domain':'strictly positive integers','witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],
 'coefficient_binding':g['coefficient_binding'],'source':prefix+tail,'output':'polynomial',
 'operations':67,'status':'candidate; reverse existence and iPRA transfer unchecked',
 'parent_graph_sha256':hashlib.sha256(raw).hexdigest()}
path=HERE/'polynomial.json'
if path.exists():raise SystemExit('refusing existing graph')
path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
