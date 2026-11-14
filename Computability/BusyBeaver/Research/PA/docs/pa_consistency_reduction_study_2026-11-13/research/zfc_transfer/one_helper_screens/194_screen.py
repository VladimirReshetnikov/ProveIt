#!/usr/bin/env python3
import json,csv,itertools,time
from pathlib import Path
ROOT=Path('/home/agent/proveit_research_repo');OUT=Path(__file__).resolve().parent/'new_helpers';OUT.mkdir(exist_ok=True)
def read(p):
 rows={};start=0
 for line in p.read_text().splitlines():
  if line.startswith('#! start'):start=int(line.split()[-1])
  line=line.split('#',1)[0].strip()
  if not line:continue
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 return rows,start

def matching(edges,protected):
 adj={}
 for a,b in edges:
  if {a,b}&protected:continue
  adj.setdefault(a,[]).append(b)
 m={}
 def aug(a,seen):
  for b in adj.get(a,[]):
   if b in seen:continue
   seen.add(b)
   if b not in m or aug(m[b],seen):m[b]=a;return True
  return False
 for a in adj:aug(a,set())
 return [(a,b) for b,a in m.items()]

def fold(rows,pairs,u,v):
 h=max(q for q,b in rows)+2
 aliases=dict(pairs);chosen={b:a for a,b in pairs};new={}
 for (q,bit),act in rows.items():
  if q in aliases:continue
  if q in chosen and act!=rows[chosen[q],bit]:act=(bit,-1,h)
  w,d,n=act;new[q,bit]=(w,d,aliases.get(n,n))
 new[h,0]=(0,1,u);new[h,1]=(1,1,v)
 for a,b in pairs:
  for origin,old in enumerate([a,b]):
   for bit in range(2):
    w,d,n=rows[old,bit];expected=(aliases.get(n,n),d,{ -1:origin,0:w})
    q,x,t=b,0,{-1:origin,0:bit}
    for k in range(1,30):
     w,d,q=new[q,t[x]];t[x]=w;x+=d
     if (q,x,t)==expected:break
     assert x in (-1,0),(pairs,u,v,origin,bit,k,q,x,t,expected)
    else:raise AssertionError('failed')
 return new,h

def run(rows,start):
 states=sorted({q for q,b in rows});inc={q:set()for q in states};bad=set()
 for (q,bit),(w,d,n)in rows.items():
  if n not in inc:continue
  if d==1:inc[n].add(w)
  else:bad.add(n)
 left=[q for q in states if inc[q]=={0} and q not in bad and q!=start]
 right=[q for q in states if inc[q]=={1}and q not in bad and q!=start]
 sigs=[{},{}]
 for q in states:
  for b in (0,1):sigs[b].setdefault(rows[q,b],set()).add(q)
 candidates={}
 for a in left:
  for b in right:
   diff=[bit for bit in(0,1)if rows[a,bit]!=rows[b,bit]]
   if not diff:continue
   us=set(states)-{a,b};vs=set(states)-{a,b}
   for bit in diff:
    us&=sigs[bit][rows[a,bit]];vs&=sigs[bit][rows[b,bit]]
   for u,v in itertools.product(us,vs):candidates.setdefault((u,v),[]).append((a,b))
 best=0;hits=[]
 for (u,v),edges in candidates.items():
  if len(edges)<2:continue
  pairs=matching(edges,{u,v})
  best=max(best,len(pairs))
  if len(pairs)>=2:
   new,h=fold(rows,pairs,u,v);hits.append(dict(helper=[h,u,v],pairs=pairs,states=len(new)//2))
 return dict(left=len(left),right=len(right),helpers=len(candidates),best_matching=best,hits=hits)
items=[];t0=time.time()
for rec in csv.DictReader((ROOT/'Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv').open(),delimiter='\t'):
 if rec['states']!='194':continue
 p=ROOT/rec['kept_file'];rows,start=read(p)
 result=run(rows,start);result.update(path=rec['kept_file'],table_class=rec['table_class'])
 items.append(result);print(len(items),rec['first_packet'],result['best_matching'],len(result['hits']),flush=True)
(OUT/'results.json').write_text(json.dumps(items,indent=2)+'\n')
print('DONE',len(items),time.time()-t0,'seconds',sum(len(x['hits'])for x in items),'hits')
