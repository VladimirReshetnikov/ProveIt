from search_folds import *
import sys
rows=read_table(Path(sys.argv[1]) if len(sys.argv)>1 else BASE/'sources/bb196/data/pa196.tm')
k=5;reach=reachable(rows,k);n=196;start=time.time();hits=[]
incoming=defaultdict(list)
for key,act in rows.items():incoming[act[2]].append((key,act))
for q in range(1,n):
 ds={a[1] for (p,b),a in incoming[q] if p!=q}
 if len(ds)!=1:continue
 shift=-2*next(iter(ds))
 for r in range(n):
  if q==r:continue
  mp=lambda s:r if s==q else s
  nr={}
  for (p,b),(w,d,t) in rows.items():
   if p==q:continue
   nr[p,b]=(w,-d if t==q else d,mp(t))
  lens={};ok=True
  for v in reach[q]:
   tp={i-k:(v>>i)&1 for i in range(2*k+1)};dst=tp.copy()
   b=tp[0];w,od,ot=rows[q,b];dst[0]=w
   target=mp(ot);th=od+(shift if ot==q else 0);s=r;h=shift
   for steps in range(1,36):
    if h not in tp or (s,tp[h]) not in nr:break
    w,d,s=nr[s,tp[h]];tp[h]=w;h+=d
    if s==target and h==th and tp==dst:
     lens.setdefault(b,set()).add(steps);break
   else:ok=False
   if not(s==target and h==th and tp==dst):ok=False
   if not ok:break
  if ok:
   hit={'drop':q,'keep':r,'head_shift':shift,'lengths':{s:sorted(v) for s,v in lens.items()}}
   hits.append(hit);print('HIT',hit,flush=True)
print('DONE',len(hits),time.time()-start,flush=True)
name=Path(sys.argv[1]).stem if len(sys.argv)>1 else 'baseline'
(BASE/f'research/offsets_{name}.json').write_text(json.dumps(hits,indent=2))
