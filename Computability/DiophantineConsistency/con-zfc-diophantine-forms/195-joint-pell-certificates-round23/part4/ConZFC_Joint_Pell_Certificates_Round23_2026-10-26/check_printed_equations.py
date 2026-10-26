#!/usr/bin/env python3
"""Round-trip printed residuals, ports, seed corrections and monic tables."""
import json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent
out={}
for name in ['check_literal_appendix.py','check_reciprocal_ledger.py']:
 p=subprocess.run([sys.executable,'-B',str(R/'audit'/name),str(R)],capture_output=True,text=True)
 if p.returncode:raise RuntimeError(p.stdout+'\n'+p.stderr)
 out[name]=json.loads(p.stdout)
print(json.dumps({'status':'PASS','printed_specifications':out},indent=2))
