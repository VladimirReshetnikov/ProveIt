from explore import *
import time
T=parse(BASE/'pa194.native.tm')
T={(q,b):(w,d,88 if n==301 else n) for(q,b),(w,d,n)in T.items()if q!=301};T[88,0]=(0,False,51);T[51,0]=(0,True,122)
cs=contracts();usage={};start=time.time()
for c in cs:
 rows=set()
 def observe(s):
  q,onl,l,r=s;b=sr.headbit(l if onl else r)
  rows.add((q,b))
 n=sr.run(T,c,observe=observe)
 if n is None:raise ValueError(('core source failure',c[0],c[1]))
 for row in rows:usage.setdefault(row,[]).append((n,c))
for row in usage:usage[row].sort(key=lambda nc:nc[0])
candidates=json.loads((BASE/'box_row_search.json').read_text())['candidates'];valid=[]
for k,cand in enumerate(candidates):
 row=tuple(cand['row']);act=tuple(cand['action']);old=T[row];T[row]=act
 used=usage.get(row,[])
 for n,c in used:
  if sr.run(T,c) is None:break
 else:
  valid.append(cand)
 T[row]=old
 if k%100==0:print(k,len(valid),time.time()-start,flush=True)
(BASE/'box_source_neutral.json').write_text(json.dumps(valid,indent=2))
(BASE/'core193.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(T.items())))
(BASE/'core193_edits.tsv').write_text(''.join(f'{i} {c["row"][0]} {c["row"][1]} {c["action"][0]} {1 if c["action"][1]else-1} {c["action"][2]}\n'for i,c in enumerate(valid)))
print('done',len(valid),time.time()-start,flush=True)
