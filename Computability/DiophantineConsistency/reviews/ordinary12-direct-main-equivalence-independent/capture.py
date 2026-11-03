#!/usr/bin/env python3
"""Capture the bounded-port equivalence audit without overwriting evidence."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize: raise SystemExit('optimized Python refused')
here=Path(__file__).resolve().parent;out=here/'observations/attempt01'
if out.exists(): raise SystemExit('observation already exists')
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
inputs=[here/'check.py',here/'capture.py'];before={str(p):sha(p) for p in inputs}
out.mkdir(parents=True)
cmd=[sys.executable,'-I','-S','-B',str(here/'check.py')]
proc=subprocess.run(cmd,capture_output=True,timeout=180)
(out/'stdout').write_bytes(proc.stdout);(out/'stderr').write_bytes(proc.stderr)
after={str(p):sha(p) for p in inputs}
if proc.returncode or proc.stderr or before!=after: raise SystemExit('audit failed or changed')
data={'command':cmd,'exit':proc.returncode,'inputs_before':before,'inputs_after':after,
      'stdout_sha256':sha(out/'stdout'),'stderr_sha256':sha(out/'stderr')}
(out/'terminal.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','inputs_unchanged':True,'exit':proc.returncode}))
