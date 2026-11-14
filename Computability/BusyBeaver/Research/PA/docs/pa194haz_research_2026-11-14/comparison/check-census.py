#!/usr/bin/env python3
"""Replay the pinned direct .tm census from retained literal bytes and path manifest."""
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/"direct-tm-file-manifest.json").read_text())
expected=json.loads((ROOT/"direct-tm-census.json").read_text())
counts={}; recognized=0; occurrences=0; total_occurrences=0; excluded=[]
for m in manifest:
    data=(ROOT/"raw-tables"/(m["blob"]+".tm")).read_bytes()
    assert hashlib.sha256(data).hexdigest()==m["raw_sha256"]
    assert hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()==m["blob"]
    rows={}; bad=False
    for line in data.decode("utf8").splitlines():
        line=line.strip()
        if not line or line.startswith("#"): continue
        a=re.fullmatch(r"(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)",line)
        if a is None: bad=True; continue
        q,b,w,d,t=a.groups(); key=(int(q),int(b))
        if key in rows: bad=True
        rows[key]=(int(w),d,int(t))
    labels={q for q,b in rows}; targets={t for w,d,t in rows.values()}
    valid=not bad and bool(labels) and len(rows)==2*len(labels) and len(targets-labels)==1
    assert len(labels)==m["states"]
    assert valid==m["valid"]
    count=sum(path.endswith(".tm") for path in m["paths"]); total_occurrences+=count
    if valid:
        recognized+=1; occurrences+=count
        bucket=counts.setdefault(str(len(labels)),{"unique_blobs":0,"occurrences":0})
        bucket["unique_blobs"]+=1; bucket["occurrences"]+=count
    else: excluded.append({"blob":m["blob"],"states":len(labels),"occurrences":count,"undefined_halt_targets":len(targets-labels)})
assert len(manifest)==expected["unique_tm_blobs"]
assert total_occurrences==expected["tm_file_occurrences"]
assert recognized==expected["recognized_unique_complete_tables"]
assert occurrences==expected["recognized_complete_table_occurrences"]
assert counts==expected["stateCounts"]
print(json.dumps({"snapshot":expected["snapshot"],"direct_file_occurrences":total_occurrences,"unique_blobs":len(manifest),"recognized_tables":recognized,"recognized_occurrences":occurrences,"state_counts":counts,"excluded":excluded},indent=2))
