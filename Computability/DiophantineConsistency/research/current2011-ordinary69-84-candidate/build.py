#!/usr/bin/env python3
"""Construct a 69-gate exact polynomial rewrite of the current 70/84 graph."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
parent=D/'research/current2011-ordinary70-84-candidate/polynomial.json';raw=parent.read_bytes()
if hashlib.sha256(raw).hexdigest()!='bb7df3586252e9c85be225a0373a8586c2c2f841683cc5f4b6f57f02175447e5':raise RuntimeError('parent hash')
g=json.loads(raw);prefix=g['source'][:61]
if prefix[-1]!=['strong_residual','-','I2','Aaux']:raise RuntimeError('prefix mismatch')
tail=[['Na2','*','Na','Na'],['PQ','*','N0','N1'],['PQW','*','PQ','Nt'],
 ['PQWminus2','-','PQW',2],['PQWproduct','*','PQW','PQWminus2'],
 ['strong2','*','strong_residual','strong_residual'],['sum1','+','Na2','strong2'],
 ['polynomial','+','sum1','PQWproduct']]
out={'schema':'literal_integer_arithmetic_dag_v1','name':'current2011_ordinary69_degree84_candidate',
 'witness_domain':'strictly positive integers','witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],
 'coefficient_binding':g['coefficient_binding'],'source':prefix+tail,'output':'polynomial','operations':69,
 'status':'candidate; Lean binding and iPRA transfer unchecked','parent_graph_sha256':hashlib.sha256(raw).hexdigest()}
target=HERE/'polynomial.json'
if target.exists():raise SystemExit('refusing existing graph')
target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
