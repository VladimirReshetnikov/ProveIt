#!/usr/bin/env python3
"""Read-only, independent graph transcription and residue checks."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for name,digest in pins.items(): assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
p=json.loads((ROOT/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
graph=(ROOT/'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src').read_text()
# Check exact order and operands of all graph rows and generated field mapping.
body=graph.split('def graph (p : Fin 4 → ℤ) : Graph :=\n',1)[1].split('\n\nend EtaNaturalUnitGraphDraft',1)[0].splitlines()
expected=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(p['witnesses'])]
expected += ['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(p['fixed_numerals'])]
expected += ['  let '+n+' := '+str(a)+' '+op+' '+str(b) for n,op,a,b in p['source']]
expected += ['  ⟨A0, A1, Fa, Fs, out, g72, qm, Z, X, s, k, U, a, c, Dstar, n_y, V, n_f, I, ell, Delta⟩']
assert body==expected
first=0
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 q=(1+b)%4;y=q*q*q*s;ell=x*y*y*k
 val=(1+z*z-b*b*(1+ell*(ell+k)))%4
 assert val!=3
 # Independent parity split explaining the exhaustive check.
 if b%2==0: assert b*b%4==0 and val==(1+z*z)%4
 else: assert y%4==0 and ell%4==0 and val==z*z%4
 first+=1
counts={}
for kind,n in [('main',4),('aux',4),('strong',3)]:
 ct=0
 for r in itertools.product(range(4),repeat=n):
  if kind=='main':
   u,a,c,d=r; value=1+d*d-u*u*(1+(3+4*a+a*a)*c*c)
  elif kind=='aux':
   y,z,a,f=r; Q=(3+4*a+a*a)*(f*f-1);value=y*y-Q*(y*y-z*z)
  else:
   I,a,f=r;value=1+I*I-(3+4*a+a*a)*(f*f-1)
  assert value%4!=3,(kind,r);ct+=1
 counts[kind]=ct
for a,b,c,d in itertools.product((-1,1),repeat=4):
 if a*b*c*d==1 and all(x!=-1 for x in (a,b,c,d)): assert (a,b,c,d)==(1,1,1,1)
print(json.dumps({'source_pins':pins,'prototype_rows':len(p['source']),
 'first_mod4_cases':first,'generic_factor_mod4_cases':counts,
 'lean_executed':False,'scope':'finite/source review only; no model/provider or graph endpoint proof'},sort_keys=True,indent=2))
