import sys,json,itertools,time,collections
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1] / "verification"))
from flexible_core import *
rows,labs=machine();cs,om=flex_contracts();uses=collections.defaultdict(set);at=0

def observe(s):
 q,onl,l,r=s
 if not onl:
  b=headbit(r)
  if b is not None:uses[q,b].add(at)
for at,c in enumerate(cs):assert run_flex(rows,c,observe=observe)is not None
print('baseline',len(cs),'observedrows',len(uses),flush=True)
protected={(q,b)for q in BOXSTATES for b in(0,1)if(q,b)in rows and(q,b)!=(113,0)}
psucc={rows[k][2]for k in protected};states=sorted({q for q,b in rows});found=[];tried=0;start=time.monotonic();failed=collections.Counter();deep=0
for ia,a in enumerate(states):
 if a in BOXSTATES or a in psucc or a==84:continue
 for b in states:
  if b==a or (b<a and b not in BOXSTATES and b not in psucc and b!=84):continue
  for pick0,pick1 in itertools.product((a,b),repeat=2):
   rr=quotient(rows,a,b)
   for bit,src in enumerate((pick0,pick1)):
    w,d,n=rows[src,bit];rr[b,bit]=(w,d,b if n==a else n)
   if any(rr.get(x)!=rows[x]for x in protected):continue
   tried+=1
   affected=uses[a,0]|uses[a,1]|uses[b,0]|uses[b,1]
   # Prioritize observations at the retainedstate andsource ofchanged rows.
   test=[]
   for q,bit in ((b,0),(b,1),(a,0),(a,1)):
    us=uses[q,bit]
    if us:test.extend((min(us),max(us)))
   test=list(dict.fromkeys(test))
   test+= [i for i,n in failed.most_common(24)if i in affected and i not in test]
   ok=True
   for i in test:
    if run_flex(rr,cs[i])is None:failed[i]+=1;ok=False;break
   if not ok:continue
   deep+=1
   for i in affected:
    if i in test:continue
    if run_flex(rr,cs[i])is None:failed[i]+=1;ok=False;break
   if not ok:continue
   ans=validate_flex(rr,cs)
   print('SURVIVOR',a,b,pick0,pick1,ans,flush=True)
   if ans['ok']:
    out={'rows':[[q,bit,*v]for(q,bit),v in sorted(rr.items())],'merge':[a,b],'rows_from':[pick0,pick1],'validation':ans,'omitted':om}
    Path(f'experiments/flex_candidate_{a}_{b}_{pick0}_{pick1}.json').write_text(json.dumps(out,indent=2));found.append([a,b,pick0,pick1])
  if tried%1000<4:print('progress',tried,'deep',deep,'seconds',time.monotonic()-start,flush=True)
Path('experiments/flex_quotients_result.json').write_text(json.dumps({'tried':tried,'deep':deep,'survivors':found,'elapsed':time.monotonic()-start,'failure_contracts':failed.most_common()},indent=2))
print('DONE',tried,deep,found,time.monotonic()-start,flush=True)
