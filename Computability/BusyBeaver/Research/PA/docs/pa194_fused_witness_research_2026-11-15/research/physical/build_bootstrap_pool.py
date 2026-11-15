#!/usr/bin/env python3
"""Reconstruct the exact expanded 364-edit startup pool."""
from pathlib import Path
import json
import search_runtime as sr
HERE=Path(__file__).resolve().parent
old=[list(map(int,line.split()))[1:]for line in (HERE/'historical_speculative_edits.tsv').read_text().splitlines()if line.strip()]
new=json.loads((HERE/'boundary_edits.json').read_text())+[r['edit']for r in json.loads((HERE/'box_edit_extended_results.json').read_text())if r['box_extended']]
new=[x for x in new if x not in old]
assert len(old)==346 and len(new)==18
(HERE/'new_box_bootstrap_edits.json').write_text(json.dumps(new,indent=2)+'\n')
pool=old+new
(HERE/'expanded_edits.tsv').write_text(''.join(' '.join(map(str,[i,*e]))+'\n'for i,e in enumerate(pool)))
(HERE/'new_edits.tsv').write_text(''.join(' '.join(map(str,[i,*e]))+'\n'for i,e in enumerate(new)))
rows={(q,b):(w,d,88 if n==301 else n)for(q,b),(w,d,n)in sr.M.items()if q!=301}
rows[88,0]=(0,-1,51);rows[51,0]=(0,1,122)
(HERE/'runtime193.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items())))
print(json.dumps({'old_edits':len(old),'new_edits':len(new),'total':len(pool)},indent=2))
