#!/usr/bin/env python3
"""Recheck arithmetic probes with every three-bit left boundary pattern."""
import json
from pathlib import Path
import search_runtime as sr
HERE=Path(__file__).resolve().parent
rows={(q,b):(w,d,88 if n==301 else n)for(q,b),(w,d,n)in sr.M.items()if q!=301}
rows[88,0]=(0,-1,51);rows[51,0]=(0,1,122)
cases=list(sr.test_cases());results=[]
for rec in json.loads((HERE/'box_edit_source_results.json').read_text()):
    if not rec['validation']['ok']:continue
    q,b,w,d,n=rec['edit'];m=dict(rows);m[q,b]=w,d,n;failed=None
    for left in range(8):
        ones={-1-i for i in range(3)if left>>i&1}
        for c in cases:
            q0,t,eq,eh,et,tag=c
            c2=q0,t|ones,eq,eh,et|ones,(left,tag)
            if not sr.run_case(m,c2):failed=(left,tag);break
        if failed:break
    r={'edit':rec['edit'],'box_extended':failed is None,'failed':failed};results.append(r);print(r)
(HERE/'box_edit_extended_results.json').write_text(json.dumps(results,indent=2)+'\n')
