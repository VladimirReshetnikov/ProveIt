import symbolic_core as c
from pathlib import Path
import itertools,json,time,collections
OUT=Path(__file__).resolve().parent
raw,labels=c.machine();inv={v:i for i,v in enumerate(labels)}
T={(inv[q],b):(w,1 if d else -1,inv[n])for(q,b),(w,d,n)in raw.items()}
ctx=json.loads((OUT/'reader_contexts.json').read_text());R=ctx['radius'];W={int(q):ws for q,ws in ctx['contexts'].items()}
Wb={(q,b):[w for w in ws if (w>>R)&1==b]for q,ws in W.items()for b in (0,1)}

def choices(keep,drop,b,limit=40):
  def image(q):return keep if q==drop else q
  # Allow separate replacement of each keep row. No interior visit to keep allowed.
  cases=[]
  for orig in (keep,drop):
    w,d,z=T[orig,b]
    for wi in Wb[orig,b]:cases.append((wi,(wi&~(1<<R))|(w<<R),R+d,image(z)))
  def good(act):
    for wi,ew,eh,eq in cases:
      nw,nd,nq=act;word=(wi&~(1<<R))|(nw<<R);h=R+nd;q=image(nq)
      for k in range(limit):
        if q==eq and h==eh and word==ew:break
        if q in (196,keep) or not 0<=h<=2*R:return False
        rd=(word>>h)&1;nw,nd,nq=T[q,rd]
        word=(word&~(1<<h))|(nw<<h);h+=nd;q=image(nq)
      else:return False
    return True
  result=[]
  for w,d in [(b,-1),(b,1),(1-b,-1),(1-b,1)]:
    for z in range(197):
      if z in(keep,drop):continue
      if good((w,d,z)):result.append((w,d,z))
  return result

pure=[q for q in W if all(T[q,b][:2]==(b,1)for b in(0,1))]
print('pure',len(pure),flush=True)
start=time.monotonic();counts=collections.Counter();sol=[]
for p,q in itertools.combinations(pure,2):
  counts['pairs']+=1
  opts0=choices(p,q,0)
  if not opts0:continue
  counts['first_survive']+=1
  opts1=choices(p,q,1)
  if not opts1:continue
  item=dict(keep=p,drop=q,row0=opts0,row1=opts1)
  print('FOUND',item,flush=True);sol.append(item)
print(dict(counts),sol,'seconds',time.monotonic()-start,flush=True)
(OUT/'exact_source_two_row_result.json').write_text(json.dumps({'counts':dict(counts),'solutions':sol,'seconds':time.monotonic()-start},indent=2)+'\n')
