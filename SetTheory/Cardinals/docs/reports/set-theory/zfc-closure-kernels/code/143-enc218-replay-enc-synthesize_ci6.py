import sys,json,time,signal,itertools
from collections import Counter
import direct_screen as D
sys.path.insert(0,str(D.D.parent/'k223_merged_runtime_audit/runtime'));import symbolic_runtime as S
p=D.D/'shared_cancellation/candidate.native.tm';T0=S.r.table(p);mp={int(q):v for q,v in json.load(open(D.D/'NATIVE_TO_LEGACY.json')).items()}
for q in {q for q,b in T0}|{254}:
 if q not in mp:mp[q]=q+1000
T={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T0.items()};ss=json.load(open(D.D.parent/'research218_source/shared_cancellation_sites.json'));L,blocks=S.prove_blocks(T);ci=[(i,s)for i,s in enumerate(ss)if s[1:]==['CI',6]and s[0].endswith('1')]
original=S.State.step;counts=Counter();per=0;current=None;results=[];best=[];began=time.monotonic();status='COMPLETE_CI6_ENTRY_SCREEN'
def instrument(self,*args):
 global per
 counts['symbolic_rules']+=1;per+=1
 if counts['symbolic_rules']>500000:raise TimeoutError('500k rule cap')
 if per>1000:raise RuntimeError('1000 per-case construction cap')
 return original(self,*args)
S.State.step=instrument;signal.signal(signal.SIGALRM,lambda *a:(_ for _ in ()).throw(TimeoutError('60 second cap')));signal.alarm(60)
try:
 Q=sorted({q for q,b in T0}-{303,304});assert len(Q)==218
 for w,d in[(1,1),(0,1),(0,-1),(1,-1)]:
  for z in Q:
   current=[w,d,z];counts['actions']+=1;T[mp[303],1]=(w,d,mp[z]);cases=[];per=0
   try:
    for i,s in ci:
     per=0;a=S.case(T,L,s,False);a.pop('rows');a.pop('trace');cases.append(dict(index=i,site=s,**a))
   except (AssertionError,KeyError,RuntimeError)as e:
    counts[type(e).__name__]+=1
    if cases:best.append(dict(action=current,passed=len(cases),error=repr(e)))
   else:results.append(dict(action=current,cases=cases));print('HIT',current,'cases',len(cases),flush=True)
except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(action=current,error=str(e))
finally:
 signal.alarm(0);S.State.step=original;D.dump('CI6_SYNTHESIS_RESULT.json',dict(status=status,counts=dict(counts),results=results,partial_passes=best,current=current,seconds=time.monotonic()-began,per_case_cap=1000,source_sha256=D.H((D.D.parent/'research218_source/shared_cancellation_sites.json').read_bytes()),table_sha256=D.H(p.read_bytes())));print(status,dict(counts),'hits',len(results),'seconds',time.monotonic()-began,flush=True)
