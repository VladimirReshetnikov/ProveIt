"""Fresh all-tape closure and exact local discriminator fold for direct09."""
import json,time,signal
from itertools import product
from collections import Counter
import direct_screen as D
import mixed_detours as M

def main():
 began=time.monotonic();p=D.D/'direct_equality_09/candidate.native.tm';T={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,m,z=line.split();T[int(q),int(b)]=(int(w),1 if m=='R'else -1,int(z))
 assert len(T)==440
 R,checks=D.closure(T,7);D.dump('DIRECT09_CLOSURE7.json',{q:sorted(v)for q,v in R.items()})
 assert {((x>>2)&1)for x in R[122]}=={1}
 assert {((x>>2)&1)for x in R[303]}=={0}
 keep,drop=122,303;phi=lambda q:keep if q==drop else q
 U={(q,b):(w,m,phi(z))for(q,b),(w,m,z)in T.items()if q!=drop};assert T[keep,0]==T[drop,0]
 cases=[]
 for role in(drop,keep):
  for x in sorted(R[role]):
   b=x>>3&1;w,m,z=T[role,b];cases.append((role,x,(phi(z),m,(x&~8)|(w<<3))))
 cases.sort(key=lambda c:((c[1]>>3&1)==0,c[0],c[1]))
 M.CAP=2_000_000;M.cnt.clear();counts=Counter();hits=[];status='COMPLETE_FINITE_DISCRIMINATOR_SCREEN';current=None
 signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('30 second watchdog')));signal.alarm(30)
 try:
  for act in product((0,1),(-1,1),sorted({q for q,b in U})):
   current=act;counts['actions']+=1;U[keep,1]=act;proof=[]
   for role,x,goal in cases:
    trace=M.sim(U,keep,x,goal)
    if isinstance(trace,str):counts[trace]+=1;break
    proof.append(dict(role=role,word=x,goal=goal,trace=trace))
   else:
    hit=dict(action=act,proof=proof);hits.append(hit)
    out=D.D/f'direct09-fold-{len(hits):02d}';out.mkdir(exist_ok=True);(out/'candidate.native.tm').write_bytes(M.enc(U));(out/'proof.json').write_text(json.dumps(hit,indent=2)+'\n');print('HIT',act,flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(action=current,error=str(e))
 finally:
  signal.alarm(0);r=dict(status=status,table_sha256=D.H(p.read_bytes()),closure_points=sum(map(len,R.values())),closure_checks=checks,contexts={q:len(R[q])for q in(122,303)},entry_predecessors={122:1,303:0},counts=dict(counts),transitions=dict(M.cnt),hits=hits,current=current,seconds=time.monotonic()-began);D.dump('DIRECT09_FOLD_RESULT.json',r);print(json.dumps({k:v for k,v in r.items()if k!='hits'}),flush=True)
if __name__=='__main__':main()
