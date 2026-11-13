#!/usr/bin/env python3
"""Run boundary modules 06–12 sequentially; stop on any rejected check."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
BOUNDARIES = HERE.parent/'compact44-low-byte-boundary-chunks'
RUNNER = BOUNDARIES/'run.py'
OBS = HERE/'observations/attempt01'
if OBS.exists(): raise RuntimeError('refusing to overwrite an earlier batch')
inputs = [RUNNER] + [BOUNDARIES/f'CompactLowByteBoundary{i:02}.lean' for i in range(6,13)]
h = lambda p: sha256(p.read_bytes()).hexdigest()
before = {str(p): h(p) for p in inputs}
OBS.mkdir(parents=True)
(OBS/'runner-source.py').write_bytes(Path(__file__).read_bytes())
rows=[]
for i in range(6,13):
    module=f'CompactLowByteBoundary{i:02}'
    out=OBS/module
    out.mkdir()
    command=[sys.executable,'-I','-B',str(RUNNER),module]
    start=time.monotonic()
    try:
        r=subprocess.run(command,capture_output=True,text=True,timeout=240)
        code,stdout,stderr=r.returncode,r.stdout,r.stderr
    except subprocess.TimeoutExpired as exc:
        code=None
        stdout=(exc.stdout or b'').decode() if isinstance(exc.stdout,bytes) else (exc.stdout or '')
        stderr=(exc.stderr or b'').decode() if isinstance(exc.stderr,bytes) else (exc.stderr or '')
    (out/'stdout').write_text(stdout);(out/'stderr').write_text(stderr)
    row={'module':module,'command':command,'exit_code':code,
         'duration_seconds':round(time.monotonic()-start,3)}
    rows.append(row)
    (out/'result.json').write_text(json.dumps(row,indent=2,sort_keys=True)+'\n')
    print(json.dumps(row,sort_keys=True),flush=True)
    if code != 0:
        break
after={str(p): h(p) for p in inputs}
result={'inputs_before':before,'inputs_after':after,'inputs_unchanged':before==after,
        'results':rows,'complete':len(rows)==7 and all(r['exit_code']==0 for r in rows)}
(OBS/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
if not result['complete'] or not result['inputs_unchanged']: raise SystemExit(1)
