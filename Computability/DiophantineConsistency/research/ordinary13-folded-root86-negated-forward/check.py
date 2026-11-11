#!/usr/bin/env python3
"""Source and exact finite scalar/root controls for forward map; no Lean."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def load(path,sha):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==sha;return json.loads(b)
p=load('research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
c=load('research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166')
for g in (p,c):
 rows=g['source']; assert [r[0] for r in rows if 'F' in r[2:]]==['qF','g28'];assert [r[0] for r in rows if 'alpha' in r[2:]]==['C','G'];assert [r[0] for r in rows if 'Bt' in r[2:]]==(['folded_kBt','folded_q3Bt'] if g is p else ['folded_q3Bt'])
def calc(g,v):
 v=v.copy()
 def get(z):return z if isinstance(z,int) else v[z]
 for n,op,x,y in g['source']:
  a,b=get(x),get(y);v[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return v
v={x:1 for x in p['witnesses']};v.update({'J':1,'F':2,'alpha':1,'X':4,'Y':256,'eta':1,'zeta':1,'r':23,'beta':3,'K0':4,'MC':1,'MF':4});a=calc(p,v)
assert a['A0']==0 and a['q']==4 and a['qm']==3 and a['Bt']==12
b=a['qm'];q=a['q'];s=v['Y']//q**3;t=a['Bt']//b;assert s==4 and t==4
vp=v.copy();vp['F']+=b;vp['alpha']+=b*b
u=calc(c,vp);bt=u['Bt'];assert bt==-240 and bt%b==0 and u['G']==a['G'] and u['R']==a['R']
tau=abs(a['Z'])//(q**3*b);sigma=a['ell']+a['k']+s-bt//b-tau;assert sigma==85 and sigma>0 and bt<0
vp['r']=sigma;z=calc(c,vp)
assert z['A0']==a['A0']==0 and z['R']==a['R'] and all(z[n]==a[n] for n in ('A1','Fam','g72','out'))
assert a['k']*bt-sigma<0
print(json.dumps({'positive_first_root_control':True,'Bt_after_shift':bt,'candidate_sigma':sigma,'rank_and_other_residuals_preserved':True,'scope':'unconditional parent-to-candidate positive existence map under beta>0 K0>=0; no converse or Lean'},sort_keys=True,indent=2))
