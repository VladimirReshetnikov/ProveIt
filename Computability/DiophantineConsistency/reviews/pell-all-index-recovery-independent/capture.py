#!/usr/bin/env python3
"""Capture the independent no-Lean review in a fresh observation."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
P=Path(__file__).resolve().parent
out=P/'observations/attempt01';out.mkdir(parents=True,exist_ok=False)
cmd=[sys.executable,'-I','-S','-B',str(P/'check.py')]
r=subprocess.run(cmd,capture_output=True)
(out/'stdout').write_bytes(r.stdout);(out/'stderr').write_bytes(r.stderr)
h=lambda b:hashlib.sha256(b).hexdigest()
t={'exit':r.returncode,'command':cmd,'check_sha256':h((P/'check.py').read_bytes()),'stdout_sha256':h(r.stdout),'stderr_sha256':h(r.stderr),'time_ns':time.time_ns(),'scope':'Independent read-only audit; no Lean replay or full ancestry scan'}
(out/'terminal.json').write_text(json.dumps(t,indent=2,sort_keys=True)+'\n')
print(json.dumps(t,indent=2));sys.exit(r.returncode)
