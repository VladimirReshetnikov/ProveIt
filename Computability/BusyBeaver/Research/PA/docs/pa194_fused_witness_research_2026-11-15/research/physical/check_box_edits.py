#!/usr/bin/env python3
import json,time
from pathlib import Path
import source_interface as si
import search_runtime as sr
HERE=Path(__file__).resolve().parent
rows={(q,b):(w,d==1,88 if n==301 else n)for(q,b),(w,d,n)in sr.M.items()if q!=301}
rows[88,0]=(0,False,51);rows[51,0]=(0,True,122)
results=[];t0=time.time()
for q,b,w,d,n in json.loads((HERE/'finite_box_edits.json').read_text()):
    m=dict(rows);m[q,b]=(w,d==1,n)
    val=si.rt.validate(m,si.cs)
    rec={'edit':[q,b,w,d,n],'validation':val};results.append(rec);print(rec,flush=True)
(HERE/'box_edit_source_results.json').write_text(json.dumps(results,indent=2)+'\n')
print('seconds',time.time()-t0)
