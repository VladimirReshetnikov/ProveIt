"""Whole-instruction symbolic check of mixed-row state quotients."""
import symbolic_core as c
from collections import defaultdict,Counter
from pathlib import Path
import json,time,itertools
OUT=Path(__file__).resolve().parent
rows,labels=c.machine();cs=c.contracts();visits=defaultdict(dict);start=time.monotonic()
for ci,cc in enumerate(cs):
 tick=0
 def obs(s):
  global tick
  if not s[1] and s[0] not in c.BOXSTATES and s[0]!=84:visits[s[0]].setdefault(ci,(tick,s))
  tick+=1
 assert c.run(rows,cc,observe=obs)is not None
print('indexed',len(visits),sum(map(len,visits.values())),time.monotonic()-start,flush=True)

def rem(T,cc,s,fuel=1024):
 _,br,_,target=cc
 for k in range(fuel):
  if s[0]==254 if target is None else c.matches(s,target):return k
  nxt=c.sstep(T,br,s)
  if nxt is None:return None
  s,_=nxt
 return None

count=Counter();sol=[]
for ix,(keep,drop)in enumerate(itertools.combinations(sorted(visits),2)):
 affected={**visits[keep]}
 for ci,entry in visits[drop].items():
  if ci not in affected or entry[0]<affected[ci][0]:affected[ci]=entry
 order=sorted(affected,key=lambda ci:len(affected[ci][1][2])+len(affected[ci][1][3]))
 image=lambda q:keep if q==drop else q
 for from_drop_bit in(0,1):
  count['candidates']+=1
  T={(q,b):(w,d,image(n))for(q,b),(w,d,n)in rows.items()if q!=drop}
  w,d,n=rows[drop,from_drop_bit];T[keep,from_drop_bit]=(w,d,image(n))
  ok=True
  for ci in order:
   s=affected[ci][1];s=(image(s[0]),*s[1:]);count['contracts_tested']+=1
   if rem(T,cs[ci],s)is None:ok=False;break
  if ok:
   item={'keep':keep,'drop':drop,'drop_bit':from_drop_bit,'affected_contracts':len(order)}
   print('FOUND',item,flush=True);sol.append(item)
   (OUT/f'row-blend-{len(sol)}.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(T.items())))
 if ix%2000==1999:print('progress',ix+1,dict(count),time.monotonic()-start,flush=True)
print('RESULT',dict(count),sol,'seconds',time.monotonic()-start,flush=True)
(OUT/'macro_row_blends_result.json').write_text(json.dumps({'counts':dict(count),'solutions':sol,'seconds':time.monotonic()-start},indent=2)+'\n')
