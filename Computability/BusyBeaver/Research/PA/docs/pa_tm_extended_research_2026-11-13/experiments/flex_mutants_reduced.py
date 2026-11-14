import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'verification'))
from flexible_core import *
from collections import defaultdict
import time
rows,labels=machine();cs,om=flex_contracts();uses=defaultdict(set);usesbit=defaultdict(set);idx=-1

def observe(s):
 q,onl,l,r=s;uses[q].add(idx)
 if not onl and r:
  b=headbit(r)
  if b is not None:usesbit[q,b].add(idx)
for idx,c in enumerate(cs):
 assert run_flex(rows,c,observe=observe)is not None
print('baseline',len(cs),'states',len(uses),'rows',len(usesbit),flush=True)
protected={(q,b)for q in BOXSTATES for b in [0,1]if(q,b)in rows and(q,b)!=(113,0)}
states=sorted({q for q,b in rows});targets=states+[254];families=[]
for a,b in itertools.permutations(states,2):
 if a==84 or b in BOXSTATES:continue
 rr=quotient(rows,a,b)
 if any(rr.get(x)!=rows[x]for x in protected):continue
 acts=[]
 for bit in[0,1]:
  w,d,n=rows[a,bit];acts.append((w,d,b if n==a else n)==rr[b,bit])
 if sum(acts)!=1:continue
 bit=0 if not acts[0] else 1
 families.append((a,b,bit,rr))
print('families',len(families),flush=True)
start=time.monotonic();tested=0;found=[];passed_first=0;failed_hist=defaultdict(int)
for fi,(a,b,bit,rr)in enumerate(families):
 affected=sorted(uses[a]|uses[b]);focused=sorted(usesbit[a,bit]|usesbit[b,bit]);tests=focused[:1]or affected[:1]
 acts=[(w,d,t)for w,d,t in itertools.product([0,1],[False,True],targets)if t!=a]
 # Cheap actions with retreat-discriminator pattern first, then all remaining.
 acts.sort(key=lambda x:(x[0]!=bit,x[1],x[2]))
 for act in acts:
  rr[b,bit]=act;tested+=1;failed=None
  for k in tests:
   if run_flex(rr,cs[k])is None:failed=k;break
  if failed is not None:
   failed_hist[cs[failed][0]]+=1
   continue
  passed_first+=1
  for k in affected:
   if k in tests:continue
   if run_flex(rr,cs[k])is None:failed=k;break
  if failed is not None:
   failed_hist[cs[failed][0]]+=1
   if len(tests)<24:tests.append(failed)
   else:tests[1:]=tests[2:]+[failed]
   continue
  ans=validate_flex(rr,cs)
  if ans['ok']:
   record={'remove':a,'keep':b,'bit':bit,'action':act,'rows':[[q,v,*x]for(q,v),x in sorted(rr.items())],'validation':ans,'omitted':om,'engine_rows_preserved':True}
   Path(f'reduced_flex_mutant_{a}_{b}_{tested}.json').write_text(json.dumps(record,indent=2));found.append((a,b,act));print('SURVIVOR',a,b,act,ans,flush=True)
 if fi%10==0:print('progress',fi,'tested',tested,'survivors',len(found),'passed_first',passed_first,'seconds',time.monotonic()-start,flush=True)
Path('reduced_flex_mutants_result.json').write_text(json.dumps({'families':len(families),'tested':tested,'survivors':found,'elapsed':time.monotonic()-start,'failed_source_histogram':dict(failed_hist),'scope':'One-row folds preserving exact engine rows; repeated-box flexible symbolic checker with inductive 0/positive preconditions.'},indent=2))
print('DONE',tested,'found',found,'seconds',time.monotonic()-start,flush=True)
