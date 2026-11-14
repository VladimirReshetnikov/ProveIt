import sys,json,collections,itertools,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1] / "verification"))
from core import *
rows,labs=machine(); cs=contracts();groups=collections.defaultdict(list)
for line in open('experiments/general_selector.log'):
 a=list(map(int,line.split()));groups[tuple(a[5:11])].append(a)
print('groups',len(groups),flush=True)
af=iter(map(int,Path('experiments/actions.dat').read_text().split()));opts={}
for qi in range(len(labs)-1):
 for bit in (0,1):
  opts[qi,bit]={tuple(next(af)for _ in range(3))for j in range(next(af))}
  w,d,n=rows[labs[qi],bit];opts[qi,bit].add((w,int(d),labs.index(n)))
failed=set(); tried=0; newq=1800
for key,es in groups.items():
 for a,b in itertools.combinations(es,2):
  if len({*a[:2],*b[:2]})!=4:continue
  
  variants=[]
  for e in (a,b):
   bit=1 if e[2]==1 else 0
   common=opts[e[0],bit]&opts[e[1],bit] if e[2]!=3 else {()}
   variants.append([e[:11]+list(co) for co in common])
  for a,b in itertools.product(*variants):
   tried+=1;aliases={labs[e[0]]:labs[e[1]] for e in (a,b)};overrides={}
   for e in (a,b):
    qa,qb,mask,fd,wmask=e[:5]
    for bit in (0,1):
     overrides[labs[qb],bit]=(wmask>>bit&1,bool(fd),newq) if mask>>bit&1 else (e[11],bool(e[12]),labs[e[13]])
   nr={}
   for (q,bit),(w,d,n) in rows.items():
    if q in aliases:continue
    w,d,n=overrides.get((q,bit),(w,d,n));nr[q,bit]=(w,d,aliases.get(n,n))
   for bit in (0,1):
    w,d,n=key[bit*3:bit*3+3];nr[newq,bit]=(w,bool(d),aliases.get(labs[n],labs[n]))
   ok=True
   for i in failed:
    if run(nr,cs[i]) is None:ok=False;break
   if not ok:continue
   print('plausible',tried,a,b,flush=True)
   ans=validate(nr,cs)
   print('result',ans,flush=True)
   if not ans['ok']:failed.add(ans['completed']);continue
   Path('experiments/selector_candidate_all.json').write_text(json.dumps({'folds':[a,b],'rows':[[q,bit,*act]for (q,bit),act in sorted(nr.items())],'symbolic':ans},indent=2))
   print('SUCCESS',len(nr)//2,flush=True);sys.exit()
print('done',tried,'counterexamples',len(failed),flush=True)
