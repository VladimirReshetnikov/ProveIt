from pathlib import Path
import os
OUTPUT = Path(os.environ.get("A202058_REPLAY_OUT", Path(__file__).resolve().parent.parent / "build/replay"))
OUTPUT.mkdir(parents=True, exist_ok=True)
import sys,time,json
Hmax=int(sys.argv[1]) if len(sys.argv)>1 else 180
maxn=int(sys.argv[2]) if len(sys.argv)>2 else Hmax-3
prev={(s,u):[1]*(s+u) for u in range(1,Hmax//2+1) for s in range(Hmax-2*u+1)}
a=[1]; count=0; start=time.time(); violations=[]
for n in range(1,min(Hmax-2,maxn)+1):
 curr={}; Hcap=Hmax-n
 for u in range(1,Hcap//2+1):
  for s in range(Hcap-2*u+1):
   m=s+u; B=prev[(s-1,u+1)] if s else []; C=prev[(s+1,u)]
   total=sum(B[:s])+sum(C[s+1:m+1]); vals=[total]
   A=prev[(s-1,u)] if s else []; D=prev[(s+1,u-1)] if u>1 else []
   for k in range(m-1):
    total += A[k]-B[k] if k<s else D[k+1]-C[k+1]
    vals.append(total)
   curr[(s,u)]=vals
 a.append(curr[(0,1)][0])
 if n>1:
  for (s,u),vals in curr.items():
   for k,fn in enumerate(vals):
    p=prev[(s,u)][k]; pp=old[(s,u)][k]
    lhs=(n+s+u-1)*p*p; rhs=(n+s+u-2)*fn*pp; count+=1
    if lhs<rhs:
     violations.append([s,u,k,n-1,str(lhs),str(rhs)])
     if len(violations)<10:print('FAIL',violations[-1],flush=True)
 old,prev=prev,curr
 if n%10==0:print('n',n,'cap',Hcap,'checks',count,'violations',len(violations),'seconds',round(time.time()-start,2),flush=True)
print('DONE',n,count,'violations',len(violations),'seconds',time.time()-start)
json.dump(a,open(str(OUTPUT / 'a_seq_m.json'),'w'))
json.dump(violations,open(str(OUTPUT / 'm_concavity_violations.json'),'w'))
