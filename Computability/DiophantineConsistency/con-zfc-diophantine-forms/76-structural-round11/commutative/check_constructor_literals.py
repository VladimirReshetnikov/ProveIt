#!/usr/bin/env python3
"""Read back all emitted coefficient monomials; not Lean elaboration."""
from pathlib import Path
from collections import defaultdict
import json,re
R=Path(__file__).resolve().parent
term=re.compile(r'\(\(\.constant \((-?\d+) : ℤ\)\)((?: \* \(\.var \(\.in[lr] \d+\)\))*)\)')
var=re.compile(r'\.var \(\.in([lr]) (\d+)\)')
def require(x,m):
 if not x:raise AssertionError(m)
def sparse(rows):
 d=defaultdict(int)
 for r in rows:d[tuple(sorted(r['monomial']))]+=r['coefficient']
 return {k:v for k,v in d.items() if v}
n=0
for data,name in [('height_shared_step.json','HeightCommutativeEquation.lean'),('height_selector_step.json','HeightSelectedCommutativeEquation.lean'),('height_boolean_step.json','HeightBooleanCommutativeEquation.lean')]:
 j=json.loads((R/data).read_text());s=(R/name).read_text()
 rows={f'h{i}':b['sum_of_squares'] for i,b in enumerate(j['horn_source']['branches'])}
 rows.update({f'e{i}':r for i,r in enumerate(j['extra_residuals'])})
 for label,expected in rows.items():
  line=next(x for x in s.splitlines() if x.startswith('  let '+label+' :'))
  rhs=line.split(':= ',1)[1];out=defaultdict(int)
  for m in term.finditer(rhs):
   names=[]
   for side,k in var.findall(m.group(2)):names.append((j['exposed_coordinates'] if side=='l' else j['witnesses'])[int(k)])
   out[tuple(sorted(names))]+=int(m.group(1))
  require(term.sub('',rhs).replace(' + ','')=='','unparsed literal')
  require({k:v for k,v in out.items() if v}==sparse(expected),'coefficient identity '+label);n+=1
 if 'selector_groups' in j and j['witness_count']==23:
  for i in range(8):
   require(f'  let l{i} := '+' * '.join(f'b{k}' if(i>>k)&1 else f'(1 - b{k})' for k in range(3)) in s,'Boolean indicator')
  for k in range(3):require(f'let g{k} := b{k} * (b{k} - 1)' in s,'Boolean guard')
 if j['witness_count']==21:
  for i in range(4):require(f'  let l{i} := '+' * '.join('(r - '+str(k)+')' for k in range(4) if k!=i) in s,'Lagrange indicator')
out={'status':'PASS','exact_sparse_literal_roundtrips':n,'constructors':3,'scope':'literal coefficient equality and selector definitions; not Lean typechecking'}
(R/'CONSTRUCTOR_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
