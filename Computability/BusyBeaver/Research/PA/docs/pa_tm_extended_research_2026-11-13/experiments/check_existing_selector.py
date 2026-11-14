import sys,json,collections,itertools,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1] / "verification"))
from core import *
rows,labs=machine(); cs=contracts();eds=[list(map(int,l.split()))for l in open('experiments/general_selector.log')]
af=iter(map(int,Path('experiments/actions.dat').read_text().split()));opts={}
for qi in range(len(labs)-1):
 for bit in (0,1):
  opts[qi,bit]={tuple(next(af)for _ in range(3))for j in range(next(af))}
  w,d,n=rows[labs[qi],bit];opts[qi,bit].add((w,int(d),labs.index(n)))
failed=set();tried=0;matched=0
for e in eds:
 for nq in range(len(labs)-1):
  if nq in e[:2] or labs[nq]in BOXSTATES:continue
  if tuple(e[5:8])not in opts[nq,0]or tuple(e[8:11])not in opts[nq,1]:continue
  matched+=1;bit=1 if e[2]==1 else 0
  common=opts[e[0],bit]&opts[e[1],bit] if e[2]!=3 else {()}
  for co in common:
   tried+=1;newq=labs[nq];qa,qb,mask,fd,wmask=e[:5];aliases={labs[qa]:labs[qb]};overrides={}
   for bit in (0,1):
    overrides[labs[qb],bit]=(wmask>>bit&1,bool(fd),newq)if mask>>bit&1 else(co[0],bool(co[1]),labs[co[2]])
    w,d,n=e[5+3*bit:8+3*bit];overrides[newq,bit]=(w,bool(d),labs[n])
   nr={}
   for(q,bit),(w,d,n)in rows.items():
    if q in aliases:continue
    w,d,n=overrides.get((q,bit),(w,d,n));nr[q,bit]=(w,d,aliases.get(n,n))
   ok=True
   for i in failed:
    if run(nr,cs[i])is None:ok=False;break
   if not ok:continue
   print('plausible',tried,e,nq,co,flush=True)
   ans=validate(nr,cs);print('result',ans,flush=True)
   if not ans['ok']:failed.add(ans['completed']);continue
   Path('experiments/existing_selector_candidate.json').write_text(json.dumps({'fold':e,'selector':newq,'rows':[[q,bit,*act]for(q,bit),act in sorted(nr.items())],'symbolic':ans},indent=2))
   print('SUCCESS',len(nr)//2,flush=True);sys.exit()
print('done',tried,matched,'counterexamples',len(failed),flush=True)
