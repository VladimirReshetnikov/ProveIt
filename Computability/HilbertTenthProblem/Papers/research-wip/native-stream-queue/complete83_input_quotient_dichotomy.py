#!/usr/bin/env python3
"""Fresh data-only checks for the native input-quotient dichotomy."""
import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

PINS = {
 'complete83_independent_gamma_scout.py': 'b67ee981d5475a745094924d6ec3cbe72dfb38e3d28d9bd2c144ff0c2a59dc18',
 'complete83_independent_gamma_scout.json': 'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md': 'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58',
 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
}

def check(value, message):
 if not value: raise ValueError(message)

def digest(data): return hashlib.sha256(data).hexdigest()

def canonical(value): return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

def read_json(path):
 def pairs(items):
  out = {}
  for key, value in items:
   check(key not in out, 'duplicate JSON key')
   out[key] = value
  return out
 return json.loads(path.read_text(), object_pairs_hook=pairs)

def evaluate(packet, values):
 env = dict(values)
 for name, op, left, right in packet['source']:
  a = env[left] if isinstance(left, str) else left
  b = env[right] if isinstance(right, str) else right
  env[name] = a*b if op == '*' else a+b if op == '+' else a-b
 return env

def pell(A, n):
 delta = A*A-1
 x, y = 1, 0
 for _ in range(n): x, y = A*x+delta*y, x+A*y
 return x, y

def audit_source(root):
 child = read_json(root/'complete83_independent_gamma_scout.json')['packet']
 parent = read_json(root/'complete84_scaled_strong_output.json')['packet']
 expected = []
 for row in parent['source']:
  if row[0] == 'gamma_sum':
   check(row == ['gamma_sum', '+', 'rho', 'sigma'], 'private parent sum')
   continue
  expected.append([row[0], row[1]] + ['sigma' if x == 'gamma_sum' else x for x in row[2:]])
 check(child['source'] == expected, 'whole literal 84 to 83 relation')
 known = set(child['free']); dependencies = {}
 for name, op, left, right in child['source']:
  check(name not in known and op in ['*', '+', '-'], 'row uniqueness')
  check(all(type(x) is int or x in known for x in [left, right]), 'topology')
  known.add(name); dependencies[name] = [left, right]
 def ancestors(start):
  seen = set(); stack = [start]
  while stack:
   x = stack.pop()
   if type(x) is str and x not in seen:
    seen.add(x); stack.extend(dependencies.get(x, []))
  return seen
 check(ancestors(child['output']) == known, 'whole source and port liveness')
 for factor in child['factors']:
  if factor != 'norm_input':
   check(not {'delta', 'rho'} & ancestors(factor), 'private input consumers')
 ct = Counter(row[1] for row in child['source'])
 check((len(child['source']), ct['*'], ct['+']+ct['-'], len(child['witnesses'])) == (83,47,36,18), 'ledger')
 cuts = {
  'gam': ['*','sigma','a4m5'], 'R14': ['+','D1','gam'],
  'R10a': ['+','ksn2','eta'], 'R12': ['+','UM','sn2'],
  'a4m5': ['+','a4',3], 'A': ['+','a_square','a4m5'],
  'odd_index': ['+','scaled_t','inner_bits'],
  'index_product': ['*','delta','A'], 'index_rhs': ['+','odd_index','index_product'],
  'difference_multiple': ['*','index_rhs','R12'],
  'exponent_partial': ['+','W','difference_multiple'],
  'modulus_multiple': ['*','rho','a4m5'],
  'exponent_rhs': ['+','exponent_partial','modulus_multiple'],
  'norm_input': ['-','mu2','scaled_kappa2'],
  'W': ['-','marked_rhs','Z'],
  'marked_rhs': ['-','C_after_alpha','scaled_t'],
  'C_after_alpha': ['-','q_minus_FZ','alpha'],
  'scaled_t': ['*','twice_cell_bits','x'],
  'polynomial': ['-','seven_units','A'],
 }
 rows = {r[0]:r[1:] for r in child['source']}
 for name, row in cuts.items(): check(rows[name] == row, 'cut '+name)
 checks = []
 for seed in range(24):
  v = {key: Fraction(((i+3)*(seed+2))%17-8, 1 if seed<12 else i%3+1) for i,key in enumerate(child['free'])}
  w = dict(v); w['sigma'] = v['sigma']-v['rho']
  e, p = evaluate(child,v), evaluate(parent,w)
  check(all(e[row[0]] == p[row[0]] for row in child['source']), 'retained whole-ring pullback')
  checks.append(digest(canonical([str(e[child['output']]),str(p[parent['output']])])) )
 return {'packet_sha256':digest(canonical(child)), 'ledger':child['ledger'],
         'authenticated_cut_rows':cuts, 'full_literal_reconstruction':True,
         'all_rows_and_ports_live':True,'input_ports_absent_from_six_other_factors':True,
         'all_ring_pullback_checks':checks}

def component_checks():
 gap = []; normal = []
 for R in [3,5,7,9]:
  for A in [2**R+4,2**R+10]:
   a=A-2; H=4*A-5; delta=A*A-1; X=2**R
   D,c=pell(A,R); _,prev=pell(A,R-1); ER=D-a*c
   nextD,nextc=pell(A,R+1); nextE=nextD-a*nextc
   check(nextE-H*c==4*c-2*prev, 'exact next-index threshold')
   gamma,rem=divmod(ER-X,H)
   check(rem==0 and 0<gamma<c,'native quotient range component')
   for q in [2,4,16]:
    check(c>q,'component c bound')
    for v in range(1,R+4):
     d,k=pell(A,v); E=d-a*k
     for W in [-q+1,0,q-1]:
      check((E-W<H*c)==(v<=R),'strict threshold component')
      check(E-W!=H*c,'threshold equality excluded')
      gap.append([A,R,q,v,W])
   for u in range(3,R,2):
    d,k=pell(A,u); Eu=d-a*k
    rho,rem=divmod(Eu-2**u,H)
    check(rem==0 and 0<rho<gamma<c,'positive literal inverse component')
    check((k-u)%delta==0 and (k-u)//delta>0,'positive input modulus component')
    check(u<R<A and A*u<2*delta,'congruence representatives')
    normal.append({'A':A,'R':R,'u':u,'rho_bits':rho.bit_length(),'c_bits':c.bit_length(),'gamma_bits':gamma.bit_length()})
 periods=[]; total=0
 for A in range(8,42,2):
  delta=A*A-1; x,y=1,0; hits={u:[] for u in [3,5,7]}
  for v in range(1,2*delta+1):
   x,y=(A*x+delta*y)%delta,(x+A*y)%delta
   for u in hits:
    if y==u: hits[u].append(v)
    check((y==u)==(v% (2*delta) in [u,A*u]),'full input residue period')
    total+=1
  periods.append({'A':A,'period':2*delta,'hits':hits})
 return {'gap_comparisons':len(gap),'gap_records_sha256':digest(canonical(gap)),
         'positive_normal_branch_components':normal,
         'complete_modular_periods':periods,'modular_comparisons':total,
         'scope':'Pell and residue components only; none is asserted to be an actual compiler history or full83 zero.'}

def build(root):
 for name,pin in PINS.items(): check(digest((root/name).read_bytes())==pin,'pin '+name)
 return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'pins':PINS,
         'source_audit':audit_source(root),'components':component_checks(),
         'theorem':{'normal_branch':'rho<c iff v=u iff rho<gamma; literal parent sigma=gamma-rho>0',
                    'other_branch':'rho>c>gamma; even v>=A*u, odd v>=u+2*Delta',
                    'language':'Unresolved. The noncanonical branch contains known same-input accepted zeros.'},
         'full_compiler_zeros_materialized':False,'new_circuit_emitted':False}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 args=ap.parse_args(); result=build(args.root)
 if args.output: args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else: check(canonical(result)==canonical(read_json(args.expect)),'type-exact receipt')
 print(json.dumps({'status':'PASS','gap_comparisons':result['components']['gap_comparisons'],'modular_comparisons':result['components']['modular_comparisons']}))
