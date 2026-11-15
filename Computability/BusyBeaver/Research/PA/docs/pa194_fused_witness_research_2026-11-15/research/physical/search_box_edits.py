#!/usr/bin/env python3
"""Enumerate single arithmetic-row replacements preserving finite box probes."""
import sys,json,time
from pathlib import Path
import search_runtime as sr
HERE=Path(__file__).resolve().parent
M={(q,b):(w,d,88 if n==301 else n)for(q,b),(w,d,n)in sr.M.items()if q!=301}
M[88,0]=(0,-1,51);M[51,0]=(0,1,122)
cases=list(sr.test_cases())
uses={key:[] for key in M}
for i,case in enumerate(cases):
    q,t,eq,eh,et,tag=case;t=set(t);h=0;seen=set()
    for step in range(5000):
        bit=int(h in t);seen.add((q,bit));w,d,q=M[q,bit]
        (t.add if w else t.discard)(h);h+=d
        if q==eq and h==eh and t==et:break
    else:raise AssertionError(tag)
    for key in seen:uses[key].append(i)
out=[];t0=time.time()
for q,b in sorted(key for key in M if key[0] in sr.BOX):
    original=M[q,b];n0=len(out)
    if not uses[q,b]:continue # interface exit rows need separate source analysis
    for w in (0,1):
        for d in (-1,1):
            for n in sr.STATES:
                if n==301 or (w,d,n)==original:continue
                M[q,b]=w,d,n
                if all(sr.run_case(M,cases[i],fuel=2000)for i in uses[q,b]):
                    out.append([q,b,w,d,n])
    M[q,b]=original
    print('row',q,b,'survivors',len(out)-n0,'cumulative',len(out),'seconds',time.time()-t0,flush=True)
(HERE/'finite_box_edits.json').write_text(json.dumps(out,indent=2)+'\n')
print('TOTAL',len(out),'seconds',time.time()-t0)
