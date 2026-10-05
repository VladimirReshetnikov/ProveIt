#!/usr/bin/env python3
"""Replay the exact checks and compare with the distributed deterministic data."""
import json, subprocess, sys
from pathlib import Path
root=Path(__file__).resolve().parent
p=root/'code/check_exact.json'
expected=json.loads(p.read_text())
subprocess.run([sys.executable,str(root/'code/check_exact.py')],check=True,cwd=root)
actual=json.loads(p.read_text())
assert actual==expected,'Exact replay differs from distributed data'
summary={k:v for k,v in actual.items() if k not in ('records','dyck_bounds')}
summary['matches_distributed_data']=True
(root/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
