#!/usr/bin/env python3
"""Bounded nine-state runtime synthesis. Fixed unbounded return interfaces.
No finite result is claimed as a universal simulation proof.
"""
import sys,json,time,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research_sub246/context_folds/vendor'))
import z3
from explore import T,B
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--steps',type=int,default=50);ap.add_argument('--edits',type=int,default=4);ap.add_argument('--cases',type=int,default=6);a=ap.parse_args()
qs=[73,83,95,109,75,48,63,112,131];ix={q:i for i,q in enumerate(qs)};n=len(qs);EXT=9
s=z3.Solver();s.set(timeout=a.seconds*1000)
w=[z3.Bool('w'+str(i)) for i in range(2*n)];d=[z3.Bool('d'+str(i)) for i in range(2*n)];t=[z3.BitVec('q'+str(i),4) for i in range(2*n)]
changed=[]
for q in qs:
 for b in (0,1):
  j=ix[q]*2+b;ow,od,oq=T[q,b];s.add(z3.ULE(t[j],EXT))
  old=z3.And(w[j]==bool(ow),d[j]==(od==1),t[j]==ix.get(oq,EXT))
  if q in [48,63,112,131]:s.add(old)
  elif(q,b)!=(75,0):changed.append(z3.Not(old))
  s.add(t[j]!=EXT) if (q,b)!=(48,0) else None
s.add(z3.Sum([z3.If(x,1,0) for x in changed])<=a.edits)
def lookup(xs,i):
 r=xs[-1]
 for j in range(len(xs)-2,-1,-1):r=z3.If(i==j,xs[j],r)
 return r
cases=[]
for vals,r,mode in [([0,0],0,'i'),([0,0],0,'z'),([1,0],0,'p'),([1,0,0],1,'i'),([1,0,0],1,'z'),([1,2,0],1,'p'),([0,1],0,'i'),([0,1],0,'z'),([3,2,1],1,'i'),([3,0,1],1,'z'),([3,2,1],1,'p')][:a.cases]:
 p=sum(v+2 for v in vals[:r]);inp=list(B(vals));inp[p+1]='0';off=8;initial=sum(1<<(off+i) for i,b in enumerate(inp) if b=='1');out=vals.copy();head=off-1;state=ix[48];origin=off;boundary=0
 if mode=='i':out[r]+=1
 if mode=='z':state=ix[112]
 if mode=='p':out[r]-=1;head=off;origin+=1;boundary=1<<off
 targets=[]
 for tail in ([[],[0],[1],[0,0],[0,1],[1,0],[1,1]] if mode=='i' else [[]]):
  targets.append(boundary|sum(1<<(origin+i) for i,b in enumerate(B(out+tail)) if b=='1'))
 cases.append(dict(vals=vals,r=r,mode=mode,initial=initial,head=head,state=state,targets=targets))
for cnum,c in enumerate(cases):
 q=[z3.BitVec(f's{cnum}_{j}',4) for j in range(a.steps+1)];h=[z3.BitVec(f'h{cnum}_{j}',6) for j in range(a.steps+1)];v=[z3.BitVec(f'v{cnum}_{j}',64) for j in range(a.steps+1)]
 s.add(q[0]==ix[73 if c['mode']=='i' else 95],h[0]==8,v[0]==c['initial'])
 for j in range(a.steps):
  done=z3.And(q[j]==c['state'],h[j]==c['head'])
  active=z3.Not(done);s.add(z3.Implies(active,z3.And(z3.ULT(q[j],n),z3.UGE(h[j],8),z3.ULT(h[j],50))))
  bit=z3.Extract(0,0,z3.LShR(v[j],z3.ZeroExt(58,h[j])));index=z3.ZeroExt(1,q[j])*2+z3.ZeroExt(4,bit)
  ww=lookup(w,index);dd=lookup(d,index);tt=lookup(t,index);mask=z3.BitVecVal(1,64)<<z3.ZeroExt(58,h[j]);vv=z3.If(ww,v[j]|mask,v[j]&~mask)
  s.add(q[j+1]==z3.If(done,q[j],tt),h[j+1]==z3.If(done,h[j],z3.If(dd,h[j]+1,h[j]-1)),v[j+1]==z3.If(done,v[j],vv))
 s.add(q[-1]==c['state'],h[-1]==c['head'],z3.Or([v[-1]==target for target in c['targets']]))
began=time.monotonic();status=s.check();out=dict(status=str(status),seconds=time.monotonic()-began,edits=a.edits,steps=a.steps,cases=cases,scope='Bounded synthesis; outputs permit zero through two newly appended spare blocks with values0/1. Fixed full standard return/rollback pairs; unknown seek/carry/tail rows; no universal claim.')
if status==z3.sat:
 m=s.model();table=[]
 for q0 in qs:
  for b in [0,1]:
   j=ix[q0]*2+b;target=m.eval(t[j]).as_long();table.append([q0,b,int(z3.is_true(m.eval(w[j]))),'R' if z3.is_true(m.eval(d[j])) else 'L',qs[target] if target<n else 7])
 out['table']=table
elif status==z3.unknown:out['reason']=s.reason_unknown()
path=Path(__file__).with_name(f'synth9_e{a.edits}_c{a.cases}_s{a.steps}.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
