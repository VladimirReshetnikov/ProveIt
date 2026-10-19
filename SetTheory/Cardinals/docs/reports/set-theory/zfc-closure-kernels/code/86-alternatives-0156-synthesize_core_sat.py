#!/usr/bin/env python3
"""Direct CNF bounded local runtime synthesis; finite evidence only."""
import sys,json,time,argparse,signal
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'research_sub246/context_folds/vendor'))
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc
from pysat.solvers import Solver
from explore import T,B
ap=argparse.ArgumentParser();ap.add_argument('--steps',type=int,default=40);ap.add_argument('--cases',type=int,default=6);ap.add_argument('--edits',type=int,default=4);ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--free-rollback-one',action='store_true');a=ap.parse_args()
qs=[73,83,95,109,75,48,63,112,131];ix={q:i for i,q in enumerate(qs)};n=len(qs);M=32;off=2
f=CNF();vp=IDPool();var=lambda:vp.id();add=lambda *x:f.append(list(x))
def onehot(xs):f.extend(CardEnc.equals(xs,1,vpool=vp,encoding=1).clauses)
def eqcond(x,y,*cond):add(*[-c for c in cond],-x,y);add(*[-c for c in cond],x,-y)
W=[var() for _ in range(2*n)];D=[var() for _ in range(2*n)];Q=[[var() for _ in range(n)]for _ in range(2*n)]
changes=[]
for q in qs:
 for b in [0,1]:
  r=2*ix[q]+b;onehot(Q[r]);ow,od,oq=T[q,b]
  fixed=q in [48,63,112,131] and not(a.free_rollback_one and(q,b)==(131,1))
  if fixed:
   add(W[r] if ow else-W[r]);add(D[r] if od==1 else-D[r])
   if oq in ix:add(Q[r][ix[oq]])
  elif (q,b)!=(75,0):
   c=var();changes.append(c)
   for l in [W[r] if ow else-W[r],D[r] if od==1 else-D[r],Q[r][ix[oq]]]:add(c,l)
f.extend(CardEnc.atmost(changes,a.edits,vpool=vp,encoding=1).clauses)
cases=[]
for vals,r,mode in [([0,0],0,'i'),([0,0],0,'z'),([1,0],0,'p'),([1,0,0],1,'i'),([1,0,0],1,'z'),([1,2,0],1,'p'),([0,1],0,'i'),([0,1],0,'z'),([3,2,1],1,'i'),([3,0,1],1,'z'),([3,2,1],1,'p')][:a.cases]:
 p=sum(v+2 for v in vals[:r]);inp=list(B(vals));inp[p+1]='0';initial={off+i for i,b in enumerate(inp) if b=='1'};out=vals.copy();head=off-1;state=ix[48];origin=off;boundary=set()
 if mode=='i':out[r]+=1
 if mode=='z':state=ix[112]
 if mode=='p':out[r]-=1;head=off;origin+=1;boundary={off}
 targets=[]
 for tail in ([[],[0],[1],[0,0],[0,1],[1,0],[1,1]] if mode=='i' else [[]]):targets.append(boundary|{origin+i for i,b in enumerate(B(out+tail)) if b=='1'})
 cases.append(dict(vals=vals,r=r,mode=mode,initial=sorted(initial),head=head,state=state,targets=[sorted(t)for t in targets]))
 S=[[var()for _ in range(n)]for j in range(a.steps+1)];H=[[var()for _ in range(M)]for j in range(a.steps+1)];V=[[var()for _ in range(M)]for j in range(a.steps+1)]
 for j in range(a.steps+1):onehot(S[j]);onehot(H[j])
 add(S[0][ix[73 if mode=='i' else 95]]);add(H[0][off])
 for h in range(M):add(V[0][h] if h in initial else-V[0][h])
 for j in range(a.steps):
  stop=var();read=var();ww=var();dd=var();rows=[var()for _ in range(2*n)]
  add(-stop,S[j][state]);add(-stop,H[j][head]);add(stop,-S[j][state],-H[j][head])
  for h in range(M):eqcond(read,V[j][h],H[j][h])
  for q in range(n):
   for b in [0,1]:
    rr=rows[2*q+b];lit=read if b else-read
    add(-rr,S[j][q]);add(-rr,lit);add(rr,-S[j][q],-lit)
    eqcond(ww,W[2*q+b],rr);eqcond(dd,D[2*q+b],rr)
    for target in range(n):eqcond(S[j+1][target],Q[2*q+b][target],rr,-stop)
  # 48/0 is external7 and may only be met at the accepted local endpoint.
  add(-rows[2*ix[48]],stop)
  for q in range(n):eqcond(S[j+1][q],S[j][q],stop)
  for h in range(M):
   eqcond(V[j+1][h],ww,H[j][h],-stop)
   eqcond(V[j+1][h],V[j][h],-H[j][h]);eqcond(V[j+1][h],V[j][h],stop)
   eqcond(H[j+1][h],H[j][h],stop)
   if h==0:add(-H[j][h],stop,dd)
   else:add(-H[j][h],stop,dd,H[j+1][h-1])
   if h==M-1:add(-H[j][h],stop,-dd)
   else:add(-H[j][h],stop,-dd,H[j+1][h+1])
   if h<off:add(-H[j][h],stop)
 add(S[-1][state]);add(H[-1][head]);choice=[var()for _ in targets];onehot(choice)
 for ch,target in zip(choice,targets):
  for h in range(M):add(-ch,V[-1][h]if h in target else-V[-1][h])
print('constructed',vp.top,len(f.clauses),flush=True)
began=time.monotonic();out=dict(scope='Bounded CNF local synthesis, not a proof of an unbounded macro or machine.',states=9,steps=a.steps,edits=a.edits,cases=cases,free_rollback_one=a.free_rollback_one,variables=vp.top,clauses=len(f.clauses))
with Solver(name='cadical300',bootstrap_with=f)as s:
 signal.signal(signal.SIGALRM,lambda n,f:s.interrupt());signal.alarm(a.seconds)
 s.conf_budget(200000)
 try: status=s.solve_limited(expect_interrupt=True)
 except KeyboardInterrupt: status=None
 signal.alarm(0);out['status']='sat'if status else'unsat'if status is False else'unknown';out['seconds']=time.monotonic()-began
 if status:
  m=set(s.get_model());table=[]
  for q in qs:
   for b in[0,1]:
    r=2*ix[q]+b;target=7 if(q,b)==(48,0)else qs[next(k for k,t in enumerate(Q[r])if t in m)];table.append([q,b,int(W[r]in m),'R'if D[r]in m else'L',target])
  out['table']=table
path=Path(__file__).with_name(f'sat9_e{a.edits}_c{a.cases}_s{a.steps}_r{int(a.free_rollback_one)}.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
