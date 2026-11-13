#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
old=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes());new=json.loads((D/'research/ordinary14-qcube85-tradeoff/candidate.json').read_bytes())
def calc(g,v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
count=0
for beta in range(1,4):
 for J in range(1,4):
  q=1+J*beta;Q=q**3
  for X in range(1,4):
   for ss in range(1,4):
    Y=Q*ss;k=2;ell=X*Y*Y*k;P0=ell+k;tau=2*X*Y*Y+1
    base={x:1 for x in old['witnesses']+old['fixed_numerals']};base.update(beta=beta,J=J,X=X,Y=Y,r=P0+ss-tau)
    z=calc(old,base);w={x:base[x] for x in new['witnesses'] if x!='s'};w.update({x:base[x] for x in new['fixed_numerals']});w['s']=ss;w['r']=P0+tau
    zz=calc(new,w);assert all(w[x]>0 for x in new['witnesses']) and z['A0']==zz['A0']==0
    assert all(z[t]==zz[t] for t in ('A1','Fa','g72','guard','guarded_out'));count+=1
s=(P/'FreshMap86To85.lean').read_text()
for t in ('OwnZeroQuotient86Draft.quotient_and_root','fresh_zero','forward_reverse','PositiveMap85To86Draft.cast_forward','Ring85To86Draft.output_eval','(hbeta : 0<beta)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-86-ownzero-quotient-draft','ordinary14-86-fresh-root-draft','ordinary14-85-to-86-positive-map-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'FreshMap86To85.lean',D/'research/ordinary14-86-ownzero-quotient-draft/OwnZeroQuotient86.lean',D/'research/ordinary14-86-fresh-root-draft/FreshRoot86.lean',D/'research/ordinary14-85-to-86-positive-map-draft/PositiveMap85To86.lean']
print(json.dumps({'scope':'source inventory, finite partial first-root transfers and draft receipt replays; no Lean invocation','finite_partial_controls':count,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
