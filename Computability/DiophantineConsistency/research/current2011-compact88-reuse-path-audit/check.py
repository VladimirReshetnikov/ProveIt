#!/usr/bin/env python3
"""Read-only, bounded source and local polynomial checks; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2]
P=Path(__file__).resolve().parent
pins=json.loads((P/'pins.json').read_text())
for path,want in pins.items():
    assert hashlib.sha256((R/path).read_bytes()).hexdigest()==want, path

def read(p): return (R/p).read_text()
def graph(p): return json.loads(read(p))
c=graph('research/ordinary13-four-square88-30/candidate.json')
n=graph('research/adaptive87-four-square-current88-30/graph.json')
a=graph('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive13_87_degree51.json')
b=graph('research/adaptive-first-root-factor87/candidate.json')
assert c['witnesses']==n['witnesses']==a['witnesses']==b['witnesses']
assert c['fixed_numerals']==n['fixed_numerals']==a['fixed_numerals']==b['fixed_numerals']
assert len(c['source'])==len(n['source'])==88 and len(a['source'])==len(b['source'])==87
assert c['source'][:28]==n['source'][:28]==a['source'][:28]==b['source'][:28]
assert c['source'][35:76]==n['source'][35:76]
assert a['source'][35:]==b['source'][35:]
assert c['source'][28:35]==a['source'][28:35] and n['source'][28:35]==b['source'][28:35]
# Exact local symbolic polynomial interpreter, with atoms at cut boundaries.
def atom(s): return {(s,):1}
def const(x): return {():x} if x else {}
def add(x,y,sign=1):
 z=x.copy()
 for k,v in y.items(): z[k]=z.get(k,0)+sign*v
 return {k:v for k,v in z.items() if v}
def mul(x,y):
 z={}
 for a,va in x.items():
  for b,vb in y.items():
   k=tuple(sorted(a+b));z[k]=z.get(k,0)+va*vb
 return {k:v for k,v in z.items() if v}
def evaluate(rows,env):
 env=env.copy()
 def val(x): return const(x) if isinstance(x,int) else env[x]
 for name,op,x,y in rows:
  a,b=val(x),val(y)
  env[name]={'+' : lambda: add(a,b), '-' : lambda: add(a,b,-1), '*' : lambda: mul(a,b)}[op]()
 return env
root={x:atom(x) for x in ['k','Bt','g31','M','Y','qm','q3']}
assert evaluate(c['source'][28:35],root)['Z']==evaluate(n['source'][28:35],root)['Z']
V,u,Q=map(atom,['V','u','Q']); g78=add(V,u); y2=mul(g78,g78)
aux={'V':V,'u':u,'Q':Q,'g78':g78,'y2':y2}
assert evaluate(c['source'][76:80],aux)['Fa']==evaluate(n['source'][76:80],aux)['Fa']
fin={x:atom(x) for x in ['A0','A1','Fa','g72']}
assert evaluate(c['source'][80:],fin)[c['output']]==evaluate(n['source'][80:],fin)[n['output']]
assert c['source'][74]==['g78','+','V','u'] and c['source'][75]==['y2','*','g78','g78']
model=read('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean')
assert 'theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V)' in model
assert '(P88FourSquare.graph CompactSymbolicModelIff.p).output' in model
assert 'theorem positiveBridge' in model
assert 'def betaNat : ℕ := 2^(67*8807)-1' in read('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean')
data=read('Lean/DiophantineConsistency/CurrentMaskData2011.lean')
assert 'def radix : ℕ := 2 ^ 47' in data and 'def beta : ℕ := radix ^ 2011 - 1' in data
assert 67*8807==590069 and 47*2011==94517 and 590069>94517
for check,receipt in [('research/ordinary13-positive88-freej-endpoint-source-audit/check.py','research/ordinary13-positive88-freej-endpoint-source-audit/receipt.json'),('research/adaptive87-four-square-current88-model-draft/check.py','research/adaptive87-four-square-current88-model-draft/result.json')]:
 out=subprocess.check_output([sys.executable,'-I','-S','-B',str(R/check)],cwd=R)
 assert out==(R/receipt).read_bytes(),check
subprocess.run([sys.executable,'-I','-S','-B',str(R/'research/ordinary13-freej87-endpoint/generate_graph.py'),'--check',str(R/'Lean/DiophantineConsistency/Compact44/FreeJ13.lean')],cwd=R,check=True,stdout=subprocess.PIPE)
print(json.dumps({'pins':len(pins),'88_rows_each':88,'87_rows_each':87,'root_aux_output_local_identities':'pass','compact_beta_exponent':590069,'current_beta_exponent':94517,'historical_checks':'reproduced','lean_run':False},sort_keys=True,indent=2))
