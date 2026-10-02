"""Compare independently rerun numerical output to the pinned reference JSON."""
from pathlib import Path
import json,sys
reference=Path(sys.argv[1]); actual=Path(sys.argv[2]); report=[]
for p in sorted(reference.glob('*.json')):
    if p.name in ('runtime-versions.json','oeis-prefixes.json'): continue
    q=actual/p.name
    if not q.exists(): raise AssertionError('Missing replay: '+p.name)
    a=json.loads(p.read_text()); b=json.loads(q.read_text())
    assert a==b, 'JSON differs: '+p.name
    report.append(p.name)
print(json.dumps({'all_reference_json_match':True,'files':report},indent=2))
