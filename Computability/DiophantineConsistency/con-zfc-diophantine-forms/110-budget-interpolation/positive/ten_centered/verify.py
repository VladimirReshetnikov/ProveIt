#!/usr/bin/env python3
"""Portable normal/-O replay; no external dependencies and no network."""
from pathlib import Path
import subprocess,sys,json,hashlib,time
R=Path(__file__).resolve().parent
mode='optimized' if sys.flags.optimize else 'normal'
records=[]
for name in ['rebuild_coefficients.py','build.py','independent_check.py','degree_specialization.py']:
    command=[sys.executable]+(['-O'] if sys.flags.optimize else [])+[str(R/name)]
    start=time.monotonic(); result=subprocess.run(command,cwd=R,capture_output=True,text=True)
    (R/'generated'/f'{mode}_{name}.stdout.txt').write_text(result.stdout)
    (R/'generated'/f'{mode}_{name}.stderr.txt').write_text(result.stderr)
    records.append({'program':name,'exit_code':result.returncode,'elapsed_seconds':round(time.monotonic()-start,6)})
    if result.returncode:raise RuntimeError(f'{name}: {result.stderr}')
receipt={'status':'PASS','python_optimization':sys.flags.optimize,'commands':records,
         'circuit_sha256':hashlib.sha256((R/'generated/p10_positive.json').read_bytes()).hexdigest(),
         'identity_receipt':json.loads((R/'generated/INDEPENDENT_CHECKS.json').read_text()),
         'degree_receipt':json.loads((R/'generated/DEGREE_SPECIALIZATIONS.json').read_text()),
         'coefficient_receipt':json.loads((R/'generated/COEFFICIENT_CHECKS.json').read_text())}
(R/'generated'/f'VERIFICATION_{mode.upper()}.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','mode':mode,'operations':126,'degree':912,'variables':10},indent=2))
