#!/usr/bin/env python3
"""Bounded physical selector rotation search outside and inside AX."""
import sys,json,time,itertools,collections,random
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_ipra/newsearch'))
import rotation_search as r
from layout import opportunities_fast,fold
CAT={tuple(k):{tuple(a) for a in aa} for k,aa in json.loads(Path('research_ipra/newsearch/leaf_actions.json').read_text())}
def leaflist(t):
 out=[]
 def visit(t,p):
  if r.leaf(t):out.append((p,t[1],t[2]));return
  visit(t[0],p+(0,));visit(t[1],p+(1,))
 visit(t,());return out

def decode_bad(rows,sites,cap=5):
 n=0
 for p,op,arg in sites:
  q,h=84,0
  for _ in range(300):
   if not 0<=h<len(p):n+=1;break
   b=p[h];a=rows[q,b]
   if h==len(p)-1 and a in CAT.get((op,arg,b),()):break
   if a[0]!=b or (a[1] and h==len(p)-1):n+=1;break
   q=a[2];h+=1 if a[1] else -1
  else:n+=1
  if n>=cap:return n
 return n
rows,_=r.machine();base=r.cfg(r.INITIAL)
queue=[(rows,r.INITIAL,[])];seen={hash(r.INITIAL)};start=time.time();tested=0;potential=0;goodlayouts=0;receipts=[];rng=random.Random(195)
for depth in range(1,7):
 nxt=[]
 for rr,tt,history in queue:
  for c in r.cands(rr,tt):
   r2,t2=r.rotate(rr,tt,c);key=hash(t2)
   if key in seen:continue
   seen.add(key);tested+=1
   ds=r.duplicates(r2)
   if ds:r2=r.merge(r2,ds)
   sites=leaflist(t2)
   # Decoder and exact source are mandatory for the retained search frontier.
   if any('0000000' in ''.join(map(str,p)) for p,*_ in sites):continue
   if decode_bad(r2,sites):continue
   if r.cfg(t2)!=base:continue
   goodlayouts+=1
   paths,shapes=r.interfaces(r2,t2)
   ops=opportunities_fast(r2,shapes)
   if len(r2)<392 or ops:
    potential+=1
    s,cs=r.contract_list(t2)
    candidates=[(r2,None)] if len(r2)<392 else []
    for a,b,opts in ops:
     for acts in itertools.product(*opts):candidates.append((fold(r2,a,b,acts),(a,b,acts)))
    for rf,fh in candidates:
     check=r.validate(rf,cs)
     print('POTENTIAL',depth,len(rf)//2,history+[c[:3]],fh,check,flush=True)
     if check['ok'] and len(rf)<392:
      Path('search_root/global_candidate195.json').write_text(json.dumps({'rows':[[q,b,*a] for(q,b),a in sorted(rf.items())],'sites':s,'history':history+[c[:3]],'fold':fh,'validation':check},indent=2));raise SystemExit()
   # Explore valid layouts broadly; random stable tie-breaking avoids one AX prefix.
   nxt.append((rng.random(),r2,t2,history+[c[:3]]))
 nxt.sort(key=lambda x:x[0]);queue=[(rr,tt,hh) for _,rr,tt,hh in nxt[:100]]
 item={'depth':depth,'tested':tested,'valid_layouts':goodlayouts,'potential':potential,'frontier':len(queue),'seconds':time.time()-start}
 receipts.append(item);Path('search_root/global_rotations.result.json').write_text(json.dumps(receipts,indent=2));print(item,flush=True)
 if not queue:break
