#!/usr/bin/env python3
"""Retain a fresh independent audit and replays of the two display checks."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
H=Path(__file__).resolve().parent;D=H.parents[1];A=D/'research/ordinary12-direct90-decimal-display'
OUT=H/'observations/attempt01'
if sys.flags.optimize or OUT.exists():raise SystemExit('optimized Python or existing observation refused')
scripts={'independent':H/'check.py','degree':D/'reviews/ordinary12-direct-main-gap-independent/degree.py',
         'author_display':A/'check_display.py','author_independent':A/'independent_check.py'}
def sha(p):return sha256(p.read_bytes()).hexdigest()
before={name:sha(path) for name,path in scripts.items()};OUT.mkdir(parents=True);runs={}
for name,path in scripts.items():
    command=[sys.executable,'-I','-S','-B',str(path)]
    p=subprocess.run(command,capture_output=True,timeout=90)
    (OUT/(name+'.stdout')).write_bytes(p.stdout);(OUT/(name+'.stderr')).write_bytes(p.stderr)
    runs[name]={'command':command,'exit':p.returncode,'stdout_sha256':sha(OUT/(name+'.stdout')),
                'stderr_sha256':sha(OUT/(name+'.stderr'))}
    if p.returncode or p.stderr:raise RuntimeError('audit failed: '+name)
    if name.startswith('author_'):
        original={'author_display':'check_display','author_independent':'independent_check'}[name]
        if p.stdout!=(A/'observations/checks01'/(original+'.stdout')).read_bytes():raise RuntimeError('replay differs: '+name)
after={name:sha(path) for name,path in scripts.items()}
if before!=after:raise RuntimeError('audit scripts changed')
(OUT/'terminal.json').write_text(json.dumps({'scripts_before':before,'scripts_after':after,'runs':runs,
    'scope':'external source/PDF checks and exact-degree computation; no Lean PDF or iPRA theorem'},indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','runs':list(runs),'author_stdout_matches_recorded':True},sort_keys=True))
