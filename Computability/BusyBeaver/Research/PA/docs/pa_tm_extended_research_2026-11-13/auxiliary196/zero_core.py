import core
from core import *
from pathlib import Path
from collections import defaultdict
inv=json.loads(Path(__file__).with_name('zero_invariants.json').read_text())

def oracle_multi(q,br,x):
 _,kind,r=x
 if kind=='none' and q in SKMAP:
  r=SKMAP[q];return (1 if r==0 else 3,('x','mark',r),False)
 if kind=='mark' and r<9:
  if q==64:return (40,('x','inc',r),False)
  if q==0 and br is not None:
   base,zeros=br
   if base is not None and base[0]==r:
    return (97,PLAIN,False)if base[1]else(40,('x','dec',r),True)
   if r in zeros:return(97,PLAIN,False)
core.oracle=oracle_multi

def source_contracts():
 ss,ins=program();cs=[];omitted=[]
 for c in core.contracts():
  i,br,st,t=c;masks=int(inv['reachable_masks'][i]);zz=inv['known_zero'][i]
  if not masks:omitted.append((i,br,'unreachable'));continue
  if br is not None:
   r=PHYSICAL.index(br[0]);vals={m>>r&1 for m in range(512)if masks>>m&1}
   if(int(not br[1]))not in vals:omitted.append((i,br,'impossible_branch'));continue
  cs.append((i,(br,frozenset(PHYSICAL[r]for r in zz)),st,t))
 return cs,omitted

def quotient(rows,a,b):
 return{(q,bit):(w,d,b if n==a else n)for(q,bit),(w,d,n)in rows.items()if q!=a}

if __name__=='__main__':
 import time
 cs,om=source_contracts();rows,labels=machine();print('contracts',len(cs),'omitted',len(om),flush=True)
 print(validate(rows,cs),flush=True)
 states=sorted({q for q,b in rows});found=[];tried=0;t0=time.time()
 for a,b in itertools.permutations(states,2):
  if a in BOXSTATES or b in BOXSTATES:continue
  rr=quotient(rows,a,b)
  def act(q,bit):
   w,d,n=rows[q,bit];return w,d,b if n==a else n
  common=sum(act(a,bit)==act(b,bit)for bit in [0,1])
  if not common:continue
  tried+=1
  if not all(rr.get((q,b))==rows[q,b] for q in BOXSTATES for b in (0,1)):continue
  ans=validate(rr,cs)
  if ans['ok']:
   out={'rows':[[q,bit,*v]for(q,bit),v in sorted(rr.items())],'merge':[a,b],'validation':ans,'contracts':len(cs),'omitted':om,'uses_zero_invariants':True}
   Path(f'zero_candidate_{a}_{b}.json').write_text(json.dumps(out,indent=2));found.append([a,b]);print('FOUND',a,b,ans,flush=True)
  if tried%50==0:print('tried',tried,'last',a,b,ans,'seconds',time.time()-t0,flush=True)
 print('DONE',tried,found,time.time()-t0,flush=True)
