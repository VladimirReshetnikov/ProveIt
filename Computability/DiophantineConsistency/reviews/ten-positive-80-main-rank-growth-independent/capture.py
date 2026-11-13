#!/usr/bin/env python3
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys,time
p=Path(__file__).resolve().parent;o=p/'observations/attempt01';o.mkdir(parents=True,exist_ok=False)
cmd=[sys.executable,'-I','-S','-B',str(p/'check.py')];r=subprocess.run(cmd,capture_output=True)
(o/'stdout').write_bytes(r.stdout);(o/'stderr').write_bytes(r.stderr)
h=lambda x:sha256(x).hexdigest()
t={'exit':r.returncode,'command':cmd,'check_sha256':h((p/'check.py').read_bytes()),'stdout_sha256':h(r.stdout),'stderr_sha256':h(r.stderr),'time_ns':time.time_ns(),'scope':'no Lean replay or full transitive ancestry scan'}
(o/'terminal.json').write_text(json.dumps(t,indent=2,sort_keys=True)+'\n');print(json.dumps(t,indent=2));sys.exit(r.returncode)
