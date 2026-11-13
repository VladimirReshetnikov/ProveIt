#!/usr/bin/env python3
"""Independent 86 field/DAG source and finite review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-first-fields-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstFields86.lean','bf15b71df553f656344d8898a1615fd466c6f31115ca7c2dfaea55bffef407f3').decode()
pin(A/'check_source.py','28d31085c7bab444ee306b8f2dd188edb4f4dbf52baf6cdd7562b21852e37d7e')
receipt=pin(A/'observation.json','c9a9759dcc404f23643a3b88054ab45003d691823537de368aa0f063bb1eb622')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-first-fields-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='eb138eb6112f9293fbacf082f9ab9277d4aa542ed4ea1e1a980ccf0458b9cfe6'
pin(D/'research/ordinary14-residue-guard86-lean-draft/P86ResidueGraph.lean','5b655c426151d999745360c8366f940198fcaa1a8408eb905b6b92285a9dcf42')
pin(D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean','92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f')
g=json.loads(pin(D/'research/ordinary14-residue-guard86/candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
for f in ('M beta v*firstP v+b beta v*v 7','ι (M beta v*v 8)',
 '(hport : (p 0 : DiffRing V)=ι beta)',
 '(hz : InternalZero (P86ResidueGraph.graph p).output v)',
 'eval (P86ResidueGraph.graph p).aux v-1=0',
 'theorem other_fields_ignore_root','(fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive'):
 assert f in src,f
rows={n:(a,b) for n,_,a,b in g['source']}
def depends(target,leaf):
 todo=[target];seen=set()
 while todo:
  n=todo.pop()
  if n==leaf:return True
  if n in seen or n not in rows:continue
  seen.add(n);todo.extend(x for x in rows[n] if isinstance(x,str))
 return False
assert depends('A0','r') and all(not depends(n,'r') for n in ('A1','Fa','g72','guard'))
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-residue-guard86-lean-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8601011)
for _ in range(500):
 v={n:rng.randrange(-5,6) for n in g['witnesses']+g['fixed_numerals']};z=calc(v)
 b=v['J']*v['beta'];q=1+b;M=q**3*b;k=v['eta']+v['zeta'];ell=v['X']*v['Y']**2*k;P=ell+k;D0=1+ell*P
 assert z['A0']==(M*P+b*v['Y']-M*v['r'])**2-M*M*D0
 v2=v.copy();v2['r']+=17;z2=calc(v2)
 assert all(z[n]==z2[n] for n in ('A1','Fa','g72','guard'))
print(json.dumps({'scope':'source and finite field controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'signed_controls':500,
 'four_root_independent_fields':True},sort_keys=True,indent=2))
