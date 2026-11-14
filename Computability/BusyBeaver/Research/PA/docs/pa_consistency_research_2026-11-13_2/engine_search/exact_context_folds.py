"""Full source-contract contexts for candidate reader merges (exploratory)."""
import symbolic_core as c
from collections import defaultdict,Counter
import itertools,json,time
from pathlib import Path
OUT=Path(__file__).resolve().parent
rows,labels=c.machine(); inv={v:i for i,v in enumerate(labels)}
# Work in original dense labels.
T={(inv[q],b):(w,1 if d else -1,inv[z]) for(q,b),(w,d,z)in rows.items()}
R=12;FULL=(1<<(2*R+1))-1
contexts=defaultdict(set)
unknown=0

def side(segs,n,count,left=False):
    out=[]
    for x in segs:
        if x[0]=='b':out.append(x[1])
        elif x[0]=='r':out.extend([x[1]]*min(count,x[2]*n+x[3]))
        else:
            if len(out)<count:return None
        if len(out)>=count:return out[:count]
    return (out+[0]*count)[:count] if left else None

def observe(s):
    global unknown
    q,onl,L,r=s;q=inv[q]
    if not q>=134 or onl:return
    for n in range(R+1):
        l=side(L,n,R,True);right=side(r,n,R+1)
        if l is None or right is None:
            unknown+=1;continue
        word=l[::-1]+right
        contexts[q].add(sum(b<<i for i,b in enumerate(word)))

start=time.monotonic()
cs=c.contracts()
print(c.validate(rows,cs,observe),time.monotonic()-start,flush=True)
print('contexts',sum(map(len,contexts.values())),'unknown',unknown,'histogram',Counter(map(len,contexts.values())),flush=True)
assert unknown==0
(OUT/'reader_contexts.json').write_text(json.dumps({'radius':R,'contexts':{str(q):sorted(ws)for q,ws in contexts.items()}},separators=(',',':'))+'\n')
# Candidate replaces drop by keep and optionally one of keep's rows.
# Check each original p/q transition against <=64 candidate literal steps,
# with all tape cells in complete (known) context preserved at endpoint.

def test(keep,drop,patchbit,patch,limit=64):
    def image(q):return keep if q==drop else q
    for orig in (keep,drop):
      for wi in contexts[orig]:
        b=(wi>>R)&1;w,d,z=T[orig,b]
        ew=(wi&~(1<<R))|(w<<R);eh=R+d;eq=image(z)
        q=keep;h=R;word=wi
        for k in range(limit):
          if not 0<=h<=2*R:break
          read=(word>>h)&1
          nw,nd,nq=patch if q==keep and read==patchbit else T[q,read]
          word=(word&~(1<<h))|(nw<<h);h+=nd;q=image(nq)
          if q==eq and h==eh and word==ew:break
          if q==196:break
        else:return False
        if q!=eq or h!=eh or word!=ew:return False
    return True

counts=Counter();solutions=[]
for keep,drop in itertools.permutations(sorted(contexts),2):
  for bit in (0,1):
    if T[keep,1-bit]!=T[drop,1-bit]:continue
    counts['pairs']+=1
    # Existing rows can be arbitrary write/direction/target; cheap read-preserving L first.
    for w,d in [(bit,-1),(bit,1),(1-bit,-1),(1-bit,1)]:
      for target in range(197):
        if target==drop:continue
        counts['candidates']+=1
        act=(w,d,target)
        if test(keep,drop,bit,act):
          item=dict(keep=keep,drop=drop,bit=bit,row=act)
          print('FOUND',item,flush=True);solutions.append(item)
print('RESULT',dict(counts),solutions,time.monotonic()-start,flush=True)
(OUT/'exact_context_one_row_result.json').write_text(json.dumps({'counts':dict(counts),'solutions':solutions,'seconds':time.monotonic()-start},indent=2)+'\n')
