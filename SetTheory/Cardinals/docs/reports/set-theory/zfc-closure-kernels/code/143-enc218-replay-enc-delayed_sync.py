"""Owned all-state unchanged-keeper delayed synchronization screen, exact patches."""
import direct_screen as D
import mixed_detours as M
from collections import Counter
import json,time,signal
CAP=5_000_000;cnt=Counter()
def tick():
 cnt['literal_transitions']+=1
 if cnt['literal_transitions']>CAP:raise TimeoutError('5 million transition cap')
def old_trace(T,q,x):
 out=[];head=0;trace=[]
 for _ in range(4):
  if head not in range(-3,4) or q==254:break
  b=(x>>(head+3))&1;w,m,z=T[q,b];trace.append([q,head,b,w,m,z]);x=(x&~(1<<(head+3)))|(w<<(head+3));q=z;head+=m;tick();out.append((q,head,x,tuple(tuple(a)for a in trace)))
 return out
def partial_endpoint_invariant(R,q,head,word):
 # All seven-cell windows compatible with the untouched arbitrary exterior.
 possible={0}
 for i in range(7):
  oldpos=head+i
  vals=[word>>oldpos&1]if 0<=oldpos<7 else (0,1)
  possible={p|(v<<i)for p in possible for v in vals}
 return possible<=R[q]
def main():
 began=time.monotonic();signal.signal(signal.SIGALRM,lambda *a:(_ for _ in ()).throw(TimeoutError('60 second watchdog')));signal.alarm(60)
 p=D.BASE/'k219.native.tm';assert D.H(p.read_bytes())=='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26';T=D.table(p);R,checks=D.closure(T,7);Q=sorted({q for q,b in T}-{0});cache={};hits=[];status='COMPLETE_DELAYED_SYNCHRONIZATION_SCREEN';current=None
 try:
  for drop in Q:
   for keep in Q:
    if drop==keep:continue
    current=dict(drop=drop,keep=keep);cnt['pairs']+=1;phi=lambda z:keep if z==drop else z;proof=[]
    for word in sorted(R[drop]):
     key=(drop,word)
     if key not in cache:cache[key]=old_trace(T,drop,word)
     goals={(phi(q),h,x):(q,tr)for q,h,x,tr in cache[key]};q=keep;head=0;x=word;trace=[];seen=set();found=False
     for _ in range(16):
      if head not in range(-3,4):cnt['patch_escape']+=1;break
      if q==254:cnt['unmatched_halt']+=1;break
      key=(q,head,x)
      if key in seen:cnt['cycle']+=1;break
      seen.add(key);b=x>>(head+3)&1;w,m,z=T[q,b];z=phi(z);trace.append([q,head,b,w,m,z]);x=(x&~(1<<(head+3)))|(w<<(head+3));q=z;head+=m;tick()
      if(q,head,x)in goals:
       oq,old=goals[q,head,x]
       assert trace and old and partial_endpoint_invariant(R,oq,head,x)
       proof.append(dict(word=word,old_trace=old,new_trace=trace,old_endpoint=[oq,head,x],new_endpoint=[q,head,x]));found=True;break
     else:cnt['new_step_cap']+=1
     if not found:break
    else:
     U={(q,b):(w,m,phi(z))for(q,b),(w,m,z)in T.items()if q!=drop};assert len(U)==436
     out=D.D/f'delayed-hit-{len(hits):03d}';out.mkdir(exist_ok=False);(out/'candidate.native.tm').write_bytes(M.enc(U));(out/'proof.json').write_text(json.dumps(dict(drop=drop,keep=keep,proof=proof),indent=2)+'\n')
     hit=dict(drop=drop,keep=keep,cases=len(proof),states=218,sha256=D.H(M.enc(U)),old_max_steps=max(len(p['old_trace'])for p in proof),new_max_steps=max(len(p['new_trace'])for p in proof));hits.append(hit);print('HIT',json.dumps(hit),flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(current=current,error=str(e))
 finally:
  signal.alarm(0);result=dict(status=status,input_sha256=D.H(p.read_bytes()),width=7,points=sum(map(len,R.values())),independent_closure_checks=checks,counts=dict(cnt),hits=hits,current=current,old_step_cap=4,new_step_cap=16,transition_cap=CAP,seconds=time.monotonic()-began);D.dump('DELAYED_RESULT.json',result);print('TERMINAL',json.dumps(result),flush=True)
if __name__=='__main__':main()
