#!/usr/bin/env python3
"""Independent fresh-root source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-fresh-root-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FreshRoot86.lean','6e90ba5c820ffb4c4ab48a78993c9145fc897e23d8d78f2667c9135118ecaa62').decode()
pin(A/'check_source.py','857f2fda26810933691c8a0357f211d40b708181aead06e2de5a3354dca5a062')
receipt=pin(A/'observation.json','db1be2b83e5664dfde9ac146296534daf99dbb037870871945a65cdcd1a272e6')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-fresh-root-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='71e991ceea74c051a31df713894e3fce9571db905cc05f7e5a18dc3bc6e70f63'
pin(D/'research/ordinary14-86-first-fields-draft/FirstFields86.lean','bf15b71df553f656344d8898a1615fd466c6f31115ca7c2dfaea55bffef407f3')
pin(D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean','92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f')
g=json.loads(pin(D/'research/ordinary14-residue-guard86/candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
for f in ('putRoot v (firstP v+tau+s)','(hY : v 7=Q beta v*s)',
 '(htau : tau*tau=radicand v)', 'first_eval p beta (putRoot v rr) hport',
 'other_fields_ignore_root p v (firstP v+tau+s)',
 'fiveSquares_eq_zero_iff','fresh_first p beta v s tau hport hY htau',
 'ho.1.trans hf.2.1','ho.2.2.2.trans hf.2.2.2.2'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-86-first-fields-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
cases=0
for beta in range(1,4):
 for J in range(1,4):
  q=1+J*beta;Q=q**3;b=J*beta;M=Q*b
  for X in range(1,4):
   for s in range(1,4):
    Y=Q*s;k=2;ell=X*Y*Y*k;P=ell+k;tau=2*X*Y*Y+1;D0=1+ell*P
    assert tau*tau==D0
    for sign in (-1,1):
     v={n:1 for n in g['witnesses']+g['fixed_numerals']};v.update(beta=beta,J=J,X=X,Y=Y,r=P+s+sign*tau)
     old=calc(v);fresh=v.copy();fresh['r']=P+tau+s;new=calc(fresh)
     assert v['r']>0 and old['A0']==new['A0']==0
     assert M*(P-fresh['r'])+b*Y==-M*tau
     assert all(old[n]==new[n] for n in ('A1','Fa','g72','guard'))
     cases+=1
print(json.dumps({'scope':'source and finite partial-root controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'partial_cases_both_signs':cases},sort_keys=True,indent=2))
