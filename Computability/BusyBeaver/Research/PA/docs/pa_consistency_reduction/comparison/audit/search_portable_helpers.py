#!/usr/bin/env python3
"""Port the two surviving U208 helper families to the PA196 literal machine.
Exploratory: candidates are accepted only by all 4959 symbolic contracts.
"""
import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import symbolic as S
m=S.load_machine();con=S.contracts();by={(c[0],c[1]):j for j,c in enumerate(con)}
first={};start=time.monotonic()
for j,(_i,_b,br,a,z) in enumerate(con):
 trace=[];ok=S.execute(m,br,a,z,record=trace)
 if not ok:raise ValueError('baseline')
 for tag,s,k in trace:
  if tag=='step' and k not in first:first[k]=j
protected={q for q,b in S.ENGINE_ROWS};protected|={S.ROOT,S.HALT,0}
to=S.LITERAL;raw=S.LABELS;tested=0;survivors=[];failures={}
for family,qa,ra,bit in [('127_124',127,124,0),('301_88',301,88,0)]:
 for flip in (False,True):
  q,r=(to[ra],to[qa]) if flip else (to[qa],to[ra])
  pi=lambda z:r if z==q else z
  merged={(u,b):(w,d,pi(v)) for (u,b),(w,d,v) in m.items() if u!=q}
  for h in range(196):
   if h in protected or h in (q,r):continue
   for donor in ([59,109,125] if family=='127_124' else [0]):
    c=dict(merged);c[r,bit]=(bit,-1,h)
    if family=='127_124':c[h,0]=(0,1,to[8]);c[h,1]=(1,1,to[donor])
    else:c[h,0]=(0,1,to[122]);c[h,1]=(1,1,h)
    edited=[k for k in c if k in m and c[k]!=m[k]]
    keys=[(h,0),(h,1),(q,0),(r,0)]+edited
    pre=list(dict.fromkeys(first[k] for k in keys if k in first))
    tested+=1;bad=None
    for j in pre:
     i,b,br,a,z=con[j]
     if S.execute(c,br,a,z) is None:bad=(i,b);break
    if bad is None:
     for i,b,br,a,z in con:
      if S.execute(c,br,a,z) is None:bad=(i,b);break
    item={'family':family,'drop':raw[q],'keep':raw[r],'helper':raw[h],'donor':donor,'failure':bad}
    if bad is None:
     survivors.append(item);out=Path(__file__).parent/f'candidate_{family}_{raw[h]}_{donor}.tm'
     out.write_text(''.join(f'{u} {b} {w} {"R" if d==1 else "L"} {v}\n' for (u,b),(w,d,v) in sorted(c.items())))
     print('SURVIVOR',item,flush=True)
    else:failures[str(bad)]=failures.get(str(bad),0)+1
 print('family complete',family,tested,'survivors',len(survivors),'seconds',time.monotonic()-start,flush=True)
report={'status':'complete','tested':tested,'survivors':survivors,'failure_histogram':failures,'seconds':time.monotonic()-start,'scope':'Two neutral helper families surviving in PA196; both representatives; one existing helper; strict donor forms; unchanged source and engine'}
(Path(__file__).parent/'portable_helper_search.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
