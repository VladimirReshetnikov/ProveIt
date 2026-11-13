#!/usr/bin/env python3
"""Finite modular controls for symbolic fixed-mask partial assignments."""
import hashlib,json,math,operator,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
pins={'research/p64-qcube72-free-main-candidate/graph.json':'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806','Lean/DiophantineConsistency/Compact44/P64Early.lean':'4db7d2153b1849d4646503244f7a5f2df031ddbeda4f135194b836ea125a02c1'}
for f,h in pins.items():
 if hashlib.sha256((root/f).read_bytes()).hexdigest()!=h: raise RuntimeError('pin mismatch '+f)
if (pow(2,590069,9)-1)%9!=4 or 590069<7: raise RuntimeError('fixed beta modular or size premise')
# Fixed-beta modular certificates: no giant masks or Pell witnesses evaluated.
mod=[]
for J,s,w,expected in ((1,1,1,1),(2,1,1,3),(1,3,3,9)):
 q=(4*J+1)%9;Y=(pow(q,3,9)*s)%9;X=(w*q)%9;H=(4*(X+1)*Y+3)%9
 if expected==1 and Y%3==0: raise RuntimeError('e=1 modular case')
 if expected==3 and not (Y==0 and H==3): raise RuntimeError('e=3 modular case')
 if expected==9 and not (Y%3==0 and H==0): raise RuntimeError('e=9 modular case')
 mod.append({'J':J,'s':s,'w':w,'q_mod_9':q,'Y_mod_9':Y,'H_mod_9':H,'e':expected})
a=json.loads((root/'research/p64-qcube72-free-main-candidate/graph.json').read_bytes());ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
count=0
for beta in range(67,158,9):
 for J,s,w,e0 in ((1,1,1,1),(2,1,1,3),(1,3,3,9)):
  q=beta*J+1;Y=q**3*s;X=w*q;U=Y*Y;H=4*(X*Y+Y)+3;e=math.gcd(U,H);mu=U//e
  if e!=e0 or H%e:raise RuntimeError('gcd case')
  for MC in (0,beta-1):
   for high in (1,beta-1):
    MF=beta+high;K=q-w;alpha=q-2;h=mu;c=2*Y+1;g=X+(X*Y+Y)*c+H//e
    vals={'beta':beta,'K0':K,'MC':MC,'MF':MF,'J':J,'F':1,'alpha':alpha,'z':1,'f':1,'i':1,'T':1,'s':s,'w':w,'t':1,'eta':1,'zeta':1,'y':1,'h':h}
    d=vals.copy()
    for name,op,x,y in a['source']:d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
    if min(vals[n] for n in a['witnesses'])<=0 or K<0:raise RuntimeError('positivity')
    if d['Lt']!=0 or d['R']+1>=q**4:raise RuntimeError('transport or rank window')
    if U*g!=U*(X+(X*Y+Y)*c)+H*h:raise RuntimeError('carrier')
    if e>1 and h%U==0:raise RuntimeError('divisibility obstruction')
    if d['A0']>-5 or d['unit_minus_one']==0 or d['polynomial']<=0:raise RuntimeError('first residual / nonzero output')
    count+=1
print(json.dumps({'status':'PASS_SYMBOLIC_MODULAR_AND_FINITE_CONTROLS','fixed_beta_mod_9':4,'cases':mod,'small_beta_dag_controls':count,'graph_and_source_pins':pins,'scope':'Fixed-beta modular proof with arbitrary mask bounds; finite analogous DAG controls, no actual full 72 zero or compact equivalence claim.'},sort_keys=True))
