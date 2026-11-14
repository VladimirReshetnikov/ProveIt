#!/usr/bin/env python3
"""Search state deletion by flipping directions of all incoming edges.
Affected entry positions differ by two cells; exact source contracts decide.
"""
import sys,json,time
from pathlib import Path
from collections import defaultdict
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine();cs=S.contracts();first=defaultdict(list);start=time.monotonic()
for c in cs:
 i,branch,br,s,t=c;trace=[];assert S.execute(m,br,s,t,record=trace)
 seen=set()
 for tag,v,row in trace:
  if tag=='step' and row not in seen:first[row].append((br,v,t,i,branch));seen.add(row)
protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS}|{S.ROOT,0}
states=sorted({q for q,b in m});incoming={q:[k for k,v in m.items() if v[2]==q and k[0]!=q] for q in states};tested=0;hits=[];counts=[]
for write in [(0,1),(1,0),(0,0),(1,1)]:
 for q in states:
  if q in protected:continue
  inc=incoming[q]
  if not inc:continue
  # All physical visits at one of the changed incoming rows.
  examples=[]
  for key in inc:examples.extend(first[key][:5])
  for r in states:
   if r==q:continue
   nm={k:((write[w],-d,r) if n==q else (w,d,n)) for k,(w,d,n) in m.items() if k[0]!=q}
   if not S.check_engine(nm):continue
   tested+=1;good=True
   for br,v,t,i,branch in examples:
    if S.execute(nm,br,v,t,fuel=1024) is None:good=False;break
   if good:
    try:summary,_=S.verify(nm)
    except AssertionError:continue
    item={'drop':q,'keep':r,'write':write,'summary':summary};hits.append(item);print('HIT',item,flush=True)
    (out/f'offset_{q}_{r}_{write[0]}{write[1]}.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(nm.items())))
  if q%20==0:print('progress',write,q,tested,len(hits),time.monotonic()-start,flush=True)
 counts.append({'write':write,'cumulative_tested':tested,'hits':list(hits),'seconds':time.monotonic()-start})
 (out/'offset_removal_results.json').write_text(json.dumps(counts,indent=2)+'\n')
 print('write complete',write,tested,len(hits),time.monotonic()-start,flush=True)
