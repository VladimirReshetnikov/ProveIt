#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes())
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
count=0
for beta in range(1,4):
 for J in range(1,4):
  q=1+J*beta;Q=q**3;b=J*beta
  for X in range(1,4):
   for ss in range(1,4):
    Y=Q*ss;k=2;ell=X*Y*Y*k;P0=ell+k;tau=2*X*Y*Y+1
    base={x:1 for x in g['witnesses']+g['fixed_numerals']};base.update(beta=beta,J=J,X=X,Y=Y,r=P0+ss-tau)
    old=calc(base);fresh=base.copy();fresh['r']=P0+tau+ss;new=calc(fresh)
    assert base['r']>0 and fresh['r']>0 and old['A0']==new['A0']==0
    assert all(old[t]==new[t] for t in ('A1','Fa','g72','guard'))
    assert (old['guarded_out']==0)==(new['guarded_out']==0);count+=1
s=(P/'FreshRoot86.lean').read_text()
for t in ('theorem fresh_first','theorem fresh_zero','other_fields_ignore_root','fiveSquares_eq_zero_iff','firstP v+tau+s','(hY : v 7=Q beta v*s)','(htau : tau*tau=radicand v)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
p=D/'research/ordinary14-86-first-fields-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'FreshRoot86.lean',p/'FirstFields86.lean',D/'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean']
print(json.dumps({'scope':'source inventory, finite partial first-root/field controls and draft receipt replay; no Lean invocation','finite_partial_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
