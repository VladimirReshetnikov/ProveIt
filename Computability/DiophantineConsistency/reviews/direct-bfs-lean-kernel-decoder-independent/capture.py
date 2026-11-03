#!/usr/bin/env python3
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
import time

here=Path(__file__).resolve().parent
out=here/'observations/attempt01'
out.mkdir(parents=True,exist_ok=False)
h=lambda b:sha256(b).hexdigest()
rows=[]
for name in ('check_receipts','check_data'):
    script=here/(name+'.py')
    cmd=[sys.executable,'-I','-S','-B',str(script)]
    result=subprocess.run(cmd,capture_output=True)
    (out/(name+'.stdout')).write_bytes(result.stdout)
    (out/(name+'.stderr')).write_bytes(result.stderr)
    rows.append({'command':cmd,'exit':result.returncode,'script_sha256':h(script.read_bytes()),
                 'stdout_sha256':h(result.stdout),'stderr_sha256':h(result.stderr)})
    if result.returncode:break
record={'exit':0 if len(rows)==2 and all(r['exit']==0 for r in rows) else 1,
        'checks':rows,'time_ns':time.time_ns(),
        'scope':'selected receipt audit and external finite table/recipe reconstruction; no Lean replay or full ancestry'}
(out/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record,indent=2))
sys.exit(record['exit'])
