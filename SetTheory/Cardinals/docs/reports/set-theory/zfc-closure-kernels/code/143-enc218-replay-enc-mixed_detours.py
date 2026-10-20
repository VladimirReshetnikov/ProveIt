"""Bounded exact-block synthesis for twelve concrete arithmetic/decoder pairings.

Every successful block reads only the seven-cell patch. Outside tape is opaque.
The source state invariant is freshly closed and independently checked.
"""
import direct_screen as D
from itertools import product
from collections import Counter
import json,time,signal
PAIRS=[(142,162),(93,103),(57,139),(17,161),(27,138),(37,194),(43,72),(107,108),(108,128),(31,108),(40,54),(24,94)]
CAP=5_000_000
cnt=Counter()
def enc(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if m==1 else "L"} {z}\n'for(q,b),(w,m,z)in sorted(t.items()))).encode()
def sim(t,keep,start,goal):
 x=start;head=0;q=keep;seen=set();trace=[]
 while True:
  if q==goal[0] and head==goal[1] and x==goal[2] and trace:return trace
  if head not in range(-3,4):return 'patch_escape'
  if (q,(x>>(head+3))&1)not in t:return 'interior_halt'
  key=(q,head,x)
  if key in seen:return 'cycle'
  if len(trace)>=64:return 'step_cap'
  seen.add(key);b=(x>>(head+3))&1;w,m,z=t[q,b]
  trace.append([q,head,b,w,m,z]);x=(x&~(1<<(head+3)))|(w<<(head+3));head+=m;q=z
  cnt['literal_transitions']+=1
  if cnt['literal_transitions']>CAP:raise TimeoutError('literal transition cap')
def main():
 begun=time.monotonic();signal.signal(signal.SIGALRM,lambda *args:(_ for _ in ()).throw(TimeoutError('60 second watchdog')));signal.alarm(60)
 p=D.BASE/'k219.native.tm';assert D.H(p.read_bytes())=='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
 T=D.table(p);R,c=D.closure(T,7);assert {q:sorted(v)for q,v in R.items()}=={int(q):v for q,v in json.loads((D.D/'CLOSURE7.json').read_text()).items()}
 Q=sorted({q for q,b in T});hits=[];reports=[];status='COMPLETE_FINITE_MIXED_ROLE_DETOUR_SCREEN';current=None
 try:
  for a,b in PAIRS:
   for drop,keep in[(a,b),(b,a)]:
    phi=lambda z:keep if z==drop else z
    mapped=lambda act:(act[0],act[1],phi(act[2]))
    same=[b for b in(0,1)if mapped(T[drop,b])==mapped(T[keep,b])];assert len(same)==1
    fixed=same[0];change=1-fixed;U={(q,b):mapped(act)for(q,b),act in T.items()if q!=drop}
    cases=[]
    for role in(drop,keep):
     for x in sorted(R[role]):
      read=(x>>3)&1;w,m,z=T[role,read];goal=(phi(z),m,(x&~8)|(w<<3));cases.append((role,x,goal))
    # Put the edited branch first; unchanged cases still checked for every hit.
    cases.sort(key=lambda v:((v[1]>>3)&1==fixed,v[0],v[1]))
    local=Counter();positive=[]
    for w,m,z in product((0,1),(-1,1),Q):
     if z==drop:continue
     act=(w,m,z);U[keep,change]=act;current=dict(drop=drop,keep=keep,read=change,action=act)
     cnt['branch_candidates']+=1;local['branch_candidates']+=1;proof=[]
     for role,x,goal in cases:
      trace=sim(U,keep,x,goal)
      if isinstance(trace,str):local[trace]+=1;break
      proof.append(dict(origin=role,word=x,endpoint=goal,trace=trace))
     else:
      hit=dict(**current,states=len(U)//2,fixed_read=fixed,fixed_action=U[keep,fixed],cases=len(proof),minimum_steps=min(len(p['trace'])for p in proof),maximum_steps=max(len(p['trace'])for p in proof))
      idx=len(hits);out=D.D/f'hit-{idx:03d}';out.mkdir(exist_ok=False);(out/'candidate.native.tm').write_bytes(enc(U));(out/'proof.json').write_text(json.dumps(dict(hit=hit,proof=proof),indent=2)+'\n');hit['sha256']=D.H(enc(U));hits.append(hit);positive.append(hit);print('HIT',json.dumps(hit),flush=True)
    reports.append(dict(drop=drop,keep=keep,counts=dict(local),hits=positive));print('PAIR',json.dumps(reports[-1]),flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(current=current,error=str(e))
 finally:
  signal.alarm(0);result=dict(status=status,input_sha256=D.H(p.read_bytes()),width=7,context_points=sum(map(len,R.values())),independent_closure_checks=c,counts=dict(cnt),reports=reports,hits=hits,current=current,seconds=time.monotonic()-begun,per_block_step_cap=64,transition_cap=CAP)
  D.dump('DETOUR_RESULT.json',result);print('TERMINAL',json.dumps(result),flush=True)
if __name__=='__main__':main()
