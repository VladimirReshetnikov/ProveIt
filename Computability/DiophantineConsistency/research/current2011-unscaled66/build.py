#!/usr/bin/env python3
"""Construct the integer-leaf 66-row shared-strong-term graph."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent.parent/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
PARENT_SHA='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
raw=PARENT.read_bytes()
if hashlib.sha256(raw).hexdigest()!=PARENT_SHA:raise RuntimeError('parent hash mismatch')
parent=json.loads(raw);rows=parent['source']
if len(rows)!=65 or rows[50]!=['V','-','f2inner','c']:raise RuntimeError('parent prefix boundary')
tail=[['i2','*','i','i'],['i2Dc2','*','i2','Dc2'],['strongTerm','*','i2Dc2','c2'],
      ['Z','-','f2','strongTerm'],['auxCoefficient','*','Delta','strongTerm'],
      ['V2','*','V','V'],['y2','*','y','y'],['squareGap','-','V2','y2'],
      ['auxProduct','*','auxCoefficient','squareGap'],['Na','+','auxProduct','y2'],
      ['product0','*','N0','N1'],['product1','*','product0','Na'],
      ['product2','*','product1','Nt'],['product3','*','product2','Z'],
      ['polynomial','-','product3',1]]
graph={'schema':'literal_integer_arithmetic_dag_v1',
       'name':'current2011_unscaled_shared_strong66_degree138',
       'parent':'../../candidates/one-page-padding-staircase-carrier65-2011/polynomial.json',
       'parent_sha256':PARENT_SHA,'source':rows[:51]+tail,'output':'polynomial',
       'witnesses':parent['witnesses'],'witness_domain':parent['witness_domain'],
       'fixed_numerals':parent['fixed_numerals'],'coefficient_binding':parent['coefficient_binding'],
       'coefficient_binding_base':'../../candidates/one-page-padding-staircase-carrier65-2011',
       'operations':66,'operation_counts':{'*':38,'+':16,'-':12},'exact_degree':138,
       'proof_scope':'Parent polynomial equals Delta times this graph; same zeros if Delta is nonzero.'}
out=HERE/'polynomial.json'
if out.exists():raise RuntimeError('refusing to overwrite graph')
out.write_text(json.dumps(graph,indent=2,sort_keys=True)+'\n')
print(hashlib.sha256(out.read_bytes()).hexdigest())
