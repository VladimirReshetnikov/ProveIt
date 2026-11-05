#!/usr/bin/env python3
"""Construct the 70-gate ordinary-strong sphere candidate."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
p=TASK/'research/current2011-ordinary67-94-candidate/polynomial.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb':raise RuntimeError('parent hash')
g=json.loads(raw);prefix=g['source'][:61]
if prefix[-1]!=['strong_residual','-','I2','Aaux']:raise RuntimeError('prefix mismatch')
tail=[['Na2','*','Na','Na'],['PQ','*','N0','N1'],['PQW','*','PQ','Nt'],['rPQW','-','PQW',1],
 ['rPQW2','*','rPQW','rPQW'],['strong2','*','strong_residual','strong_residual'],
 ['sum1','+','Na2','rPQW2'],['sum2','+','sum1','strong2'],['polynomial','-','sum2',1]]
binding=dict(g['coefficient_binding']);binding['path']='../fourteen-nonzero-spheres/coefficients/'
out={'schema':'literal_integer_arithmetic_dag_v1','name':'current2011_ordinary70_degree84_candidate',
 'witness_domain':'strictly positive integers','witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],
 'coefficient_binding':binding,'source':prefix+tail,'output':'polynomial','operations':70,
 'status':'candidate; all-model and iPRA equivalence unchecked','parent_graph_sha256':hashlib.sha256(raw).hexdigest()}
p=HERE/'polynomial.json'
if p.exists():raise SystemExit('refusing existing graph')
p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
