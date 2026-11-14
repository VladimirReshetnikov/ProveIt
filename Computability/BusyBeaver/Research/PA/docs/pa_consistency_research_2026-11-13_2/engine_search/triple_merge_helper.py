"""Try three reader-state identifications paid for by one fresh helper."""
import symbolic_core as c
from collections import defaultdict,Counter
from pathlib import Path
import itertools,json,time
OUT=Path(__file__).resolve().parent
raw,labels=c.machine();inv={v:i for i,v in enumerate(labels)}
T={(inv[q],b):(w,1 if d else -1,inv[n])for(q,b),(w,d,n)in raw.items()}
data=json.loads((OUT/'all_reader_contexts.json').read_text());R=data['radius']
ctx={int(q):ws for q,ws in data['contexts'].items()if int(q)!=75}

# At the first helper entry all readings are from the immediately preceding cell.
def choices(group,b,v,limit=40):
 keep=group[0];drops=group[1:]
 image=lambda q:keep if q in drops else q
 cases=[]
 for orig in group:
  ow,od,oz=T[orig,b]
  for wi,mask in ctx[orig]:
   if (wi>>R)&1!=b or (wi>>(R-1))&1!=v:continue
   ew=(wi&~(1<<R))|ow<<R;eh=R+od;eq=image(oz)
   cases.append((wi,mask,ew,eh,eq))
 if not cases:return [(v,1,0)]
 def test(act):
  for wi,mask,ew,eh,eq in cases:
   nw,nd,nq=act;word=(wi&~(1<<(R-1)))|nw<<(R-1);h=R-1+nd;q=image(nq)
   for k in range(limit):
    if h==eh and q==eq and word==ew:break
    if q==196 or not 0<=h<=2*R or not(mask>>h&1):return False
    rd=word>>h&1
    if q==keep and rd==b:return False
    nw,nd,nq=T[q,rd];word=(word&~(1<<h))|nw<<h;h+=nd;q=image(nq)
   else:return False
  return True
 result=[]
 for w,d in [(v,1),(v,-1),(1-v,1),(1-v,-1)]:
  for q in range(197):
   if q in drops:continue
   act=(w,d,q)
   if test(act):result.append(act)
 return result

start=time.monotonic();cnt=Counter();sol=[]
for b in(0,1):
 groups=defaultdict(list)
 for q in ctx:groups[T[q,1-b]].append(q)
 for row,qs in groups.items():
  if len(qs)<3:continue
  for group in itertools.combinations(qs,3):
   cnt['triples']+=1
   ch0=choices(group,b,0)
   if not ch0:continue
   cnt['first_survive']+=1
   ch1=choices(group,b,1)
   if not ch1:continue
   item=dict(group=group,bit=b,row0=ch0,row1=ch1)
   print('FOUND',item,flush=True);sol.append(item)
print('RESULT',dict(cnt),sol,'seconds',time.monotonic()-start,flush=True)
(OUT/'triple_merge_helper_result.json').write_text(json.dumps({'counts':dict(cnt),'solutions':sol,'seconds':time.monotonic()-start},indent=2)+'\n')
