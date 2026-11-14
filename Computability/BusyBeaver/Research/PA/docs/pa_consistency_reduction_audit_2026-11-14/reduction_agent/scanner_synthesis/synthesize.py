from pathlib import Path
import argparse,json,time,math
import z3 as z
ap=argparse.ArgumentParser();ap.add_argument('--states',type=int,default=6);ap.add_argument('--steps',type=int,default=24);ap.add_argument('--seconds',type=int,default=50);ap.add_argument('--readonly',action='store_true');ap.add_argument('--control',action='store_true');ap.add_argument('--symmetry',action='store_true');a=ap.parse_args()
n=a.states;left=n;right=n+1;end=n+2;qb=end.bit_length()
S=z.SolverFor('QF_AUFBV');S.set(timeout=a.seconds*1000)
A=z.Array('trans',z.BitVecSort(qb+1),z.BitVecSort(qb+2))
def act(w,d,q):return z.BitVecVal(q+(int(d)<<qb)+(w<<(qb+1)),qb+2)
def key(q,b):return z.BitVecVal(2*q+b,qb+1)
for q in range(n+2):
 for b in (0,1):
  tr=A[key(q,b)];S.add(z.ULE(z.Extract(qb-1,0,tr),end))
  if a.readonly:S.add(z.Extract(qb+1,qb+1,tr)==b)
for b in (0,1):
 S.add(A[key(left,b)]==act(b,False,left if b==0 else 0))
 S.add(A[key(right,b)]==act(b,True,right if b==0 else end))
S.add(A[key(0,1)]==act(1,False,0))
if a.symmetry:S.add(z.Extract(qb-1,0,A[key(0,0)])==1)
if a.control:
 assert n==7
 for q in range(n):
  S.add(A[key(q,0)]==act(0,False,q+1 if q<6 else right),A[key(q,1)]==act(1,False,0))
examples=[(f'run{m}',m+2,(1<<0)|(1<<(m+1)),m,0)for m in range(7)]
examples.append(('threshold',8,128,6,right))
for name,width,init,h0,targetq in examples:
 hb=max(2,width.bit_length()+1);minusone=(1<<hb)-1
 qs=[z.BitVec(f'{name}_q{t}',qb)for t in range(a.steps+1)]
 hs=[z.BitVec(f'{name}_h{t}',hb)for t in range(a.steps+1)]
 ts=[z.BitVec(f'{name}_t{t}',width)for t in range(a.steps+1)]
 done=[z.Bool(f'{name}_done{t}')for t in range(a.steps+1)]
 S.add(qs[0]==0,hs[0]==h0,ts[0]==init,z.Not(done[0]))
 for t in range(a.steps):
  S.add(z.Implies(z.Not(done[t]),z.And(z.ULT(hs[t],width),z.ULT(qs[t],end))))
  shift=z.ZeroExt(width-hb,hs[t]) if width>=hb else z.Extract(width-1,0,hs[t])
  bit=z.Extract(0,0,z.LShR(ts[t],shift));tr=A[z.Concat(qs[t],bit)]
  mask=z.BitVecVal(1,width)<<shift;nt=z.If(z.Extract(qb+1,qb+1,tr)==1,ts[t]|mask,ts[t]&~mask)
  nq=z.Extract(qb-1,0,tr);nh=hs[t]+z.If(z.Extract(qb,qb,tr)==1,z.BitVecVal(1,hb),z.BitVecVal(-1,hb))
  S.add(qs[t+1]==z.If(done[t],qs[t],nq),hs[t+1]==z.If(done[t],hs[t],nh),ts[t+1]==z.If(done[t],ts[t],nt))
  S.add(done[t+1]==z.Or(done[t],z.And(qs[t+1]==targetq,hs[t+1]==minusone,ts[t+1]==init)))
 S.add(done[-1])
print('SEARCH',vars(a),'constraints',len(S.assertions()),flush=True)
start=time.time();result=S.check();print('RESULT',result,'elapsed',time.time()-start,flush=True)
if result==z.sat:
 M=S.model();rows=[]
 for q in range(n+2):
  for b in (0,1):
   v=M.eval(A[key(q,b)]).as_long();rows.append((q,b,(v>>(qb+1))&1,1 if v&(1<<qb) else -1,v&((1<<qb)-1)))
 print(json.dumps(rows,indent=2))
 Path(f'scanner_bv_{n}.json').write_text(json.dumps({'rows':rows,'steps':a.steps,'examples':examples},indent=2))
