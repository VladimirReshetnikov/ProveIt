#!/usr/bin/env python3
"""Source-contract screen for BOX rows unvisited inside the four box excursions."""
import json,time
from pathlib import Path
import source_interface as si
import search_runtime as sr
HERE=Path(__file__).resolve().parent
rows={(q,b):(w,d==1,88 if n==301 else n)for(q,b),(w,d,n)in sr.M.items()if q!=301}
rows[88,0]=(0,False,51);rows[51,0]=(0,True,122)
keys=[(3,0),(16,0),(16,1),(40,0),(60,1),(113,0)]
uses={key:[] for key in keys}
for i,c in enumerate(si.cs):
    visited=set()
    def observe(s):
        q,onl,left,right=s
        segs=left if onl else right
        if not segs:b=0
        elif segs[0][0] in ('b','r'):b=segs[0][1]
        else:return
        visited.add((q,b))
    assert si.rt.run(rows,c,observe=observe) is not None
    for key in keys:
        if key in visited:uses[key].append(i)
out=[];stats=[];t0=time.time()
for key in keys:
    original=rows[key];n0=len(out)
    for w in (0,1):
        for d in (False,True):
            for n in sr.STATES:
                if n==301 or (w,d,n)==original:continue
                rows[key]=w,d,n
                if all(si.rt.run(rows,si.cs[i]) is not None for i in uses[key]):
                    out.append([*key,w,1 if d else -1,n]);print('PASS',out[-1],flush=True)
    rows[key]=original
    rec={'row':key,'affected_contracts':len(uses[key]),'survivors':len(out)-n0,'seconds':time.time()-t0}
    stats.append(rec);print('ROW',rec,flush=True)
    (HERE/'boundary_edits.json').write_text(json.dumps(out,indent=2)+'\n')
    (HERE/'boundary_edit_stats.json').write_text(json.dumps(stats,indent=2)+'\n')
