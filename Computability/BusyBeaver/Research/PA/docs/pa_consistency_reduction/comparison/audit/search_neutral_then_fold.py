#!/usr/bin/env python3
"""Apply a proved neutral helper redesign to PA196 and search a second fold.
The four layouts are the two surviving families, with three donor choices.
Every accepted table must pass all-natural source contracts.
"""
import sys,json,time
from pathlib import Path
from collections import defaultdict
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import symbolic as S
out=Path(__file__).parent;m0=S.load_machine();cs=S.contracts();start=time.monotonic();allresults=[]
for qa,ra,donor in [(127,124,59),(127,124,109),(127,124,125),(301,88,0)]:
 q,r=S.LITERAL[qa],S.LITERAL[ra];helper=197
 m={k:(w,d,r if n==q else n) for k,(w,d,n) in m0.items() if k[0]!=q}
 m[r,0]=(0,-1,helper)
 if qa==127:m[helper,0]=(0,1,S.LITERAL[8]);m[helper,1]=(1,1,S.LITERAL[donor])
 else:m[helper,0]=(0,1,S.LITERAL[122]);m[helper,1]=(1,1,helper)
 summary,_=S.verify(m);print('neutral verified',qa,ra,donor,summary,flush=True)
 first=defaultdict(list)
 for c in cs:
  i,branch,br,s,t=c;trace=[];assert S.execute(m,br,s,t,record=trace)
  seen=set()
  for tag,v,row in trace:
   u=v[0]
   if tag=='step' and u not in seen:first[u].append((br,v,t,i,branch));seen.add(u)
 protected={u for u,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS}|{S.ROOT,0}
 states=sorted({u for u,b in m});tested=0;hits=[]
 for drop in states:
  if drop in protected:continue
  examples=first[drop]
  for keep in states:
   if keep==drop:continue
   nm={k:(w,d,keep if n==drop else n) for k,(w,d,n) in m.items() if k[0]!=drop}
   if not S.check_engine(nm):continue
   good=True
   for br,v,t,i,branch in examples:
    v=(keep,)+v[1:]
    if S.execute(nm,br,v,t,fuel=1024) is None:good=False;break
   tested+=1
   if good:
    checked,_=S.verify(nm);item={'drop':drop,'keep':keep,'summary':checked};hits.append(item)
    print('HIT',qa,ra,donor,item,flush=True)
    (out/f'neutral_fold_{qa}_{donor}_{drop}_{keep}.tm').write_text(''.join(f'{u} {b} {w} {"R" if d==1 else "L"} {v}\n' for (u,b),(w,d,v) in sorted(nm.items())))
 print('done',qa,ra,donor,tested,hits,time.monotonic()-start,flush=True)
 allresults.append({'neutral':[qa,ra,donor],'neutral_summary':summary,'direct_folds_tested':tested,'hits':hits})
 (out/'neutral_then_fold_results.json').write_text(json.dumps(allresults,indent=2)+'\n')
