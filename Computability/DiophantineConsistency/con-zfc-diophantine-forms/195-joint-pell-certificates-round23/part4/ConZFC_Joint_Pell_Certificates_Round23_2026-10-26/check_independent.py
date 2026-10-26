#!/usr/bin/env python3
"""Independent component closure, all collected coefficients and literal ports."""
import json,os,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent
commands=[['check_source_closure.py',str(R)],['recollect_polynomials.py',str(R)],['check_positive_payloads.py',str(R/'scalar')],['check_scalar_degree.py',str(R/'scalar')]]
out={};prefix=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
for command in commands:
 p=subprocess.run(prefix+[str(R/'audit'/command[0])]+command[1:],capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 if p.returncode:raise RuntimeError(command[0]+'\n'+p.stdout+'\n'+p.stderr)
 out[command[0]]=json.loads(p.stdout)
print(json.dumps({'status':'PASS','independent_audits':out},indent=2))
