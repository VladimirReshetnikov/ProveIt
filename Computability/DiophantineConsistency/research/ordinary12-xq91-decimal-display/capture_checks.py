#!/usr/bin/env python3
"""Capture separate external display checks without modifying checked inputs."""
from hashlib import sha256
from pathlib import Path
import json, subprocess, sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
 raise SystemExit('invoke python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent;D=H.parents[1];out=H/'observations/checks01'
if out.exists():raise SystemExit('refusing to overwrite checks01')
inputs=[H/'generate.py',H/'check_display.py',H/'independent_check.py',H/'equation.tex',H/'equation.pdf',
        H/'build01/equation.tex',H/'build01/equation.pdf',H/'build02/equation.tex',H/'build02/equation.pdf',
        D/'equation.tex',D/'equation.pdf',D/'research/ordinary12-xq91-candidate/candidate.json',Path(__file__)]
def sha(p):return sha256(p.read_bytes()).hexdigest()
before={str(p):sha(p) for p in inputs};out.mkdir(parents=True);checks=[]
for name in ('check_display','independent_check'):
 cmd=[sys.executable,'-I','-S','-B',str(H/(name+'.py'))];r=subprocess.run(cmd,capture_output=True,check=True)
 (out/(name+'.stdout')).write_bytes(r.stdout);(out/(name+'.stderr')).write_bytes(r.stderr)
 if r.stderr:raise RuntimeError('unexpected stderr '+name)
 checks.append({'name':name,'command':cmd,'exit':r.returncode,'stdout_sha256':sha(out/(name+'.stdout')),'stderr_sha256':sha(out/(name+'.stderr'))})
after={str(p):sha(p) for p in inputs}
if before!=after:raise RuntimeError('input drift')
result={'checks':checks,'input_sha256_before':before,'input_sha256_after':after,'scope':'external extraction and finite coefficient checks only'}
(out/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','checks':[x['name'] for x in checks],'inputs_unchanged':before==after},indent=2))
