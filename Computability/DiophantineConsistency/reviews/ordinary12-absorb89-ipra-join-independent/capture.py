#!/usr/bin/env python3
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
H=Path(__file__).resolve().parent;S=H/'check.py';O=H/'observations/attempt01'
if sys.flags.optimize or O.exists():raise SystemExit('optimized Python or existing observation refused')
def sha(p):return sha256(p.read_bytes()).hexdigest()
digest=sha(S);O.mkdir(parents=True)
cmd=[sys.executable,'-I','-S','-B',str(S)];r=subprocess.run(cmd,capture_output=True,timeout=180)
(O/'stdout').write_bytes(r.stdout);(O/'stderr').write_bytes(r.stderr)
if r.returncode or r.stderr or sha(S)!=digest:raise RuntimeError('audit failed or changed')
(O/'terminal.json').write_text(json.dumps({'command':cmd,'exit':r.returncode,'script_sha256':digest,
 'stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr'),'scope':'external retained evidence audit; no Lean'},indent=2,sort_keys=True)+'\n')
print('PASS')
