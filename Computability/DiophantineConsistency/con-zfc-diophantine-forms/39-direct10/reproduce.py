#!/usr/bin/env python3
"""Reproduce the finite direct-quadratic certificate, from any working directory."""
from pathlib import Path
import subprocess, sys, json
ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError('Run without -O: assertion checks must remain enabled.')
for script,receipt in [('coefficients/build_coefficients.py','coefficients_rebuild.json'),
                       ('code/build_direct10.py','build.json'),
                       ('code/verify_direct10.py','verify_stdout.json'),
                       ('verification/audit_independent.py','independent_stdout.json')]:
    result=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,
                          text=True,capture_output=True)
    (ROOT/'verification'/receipt).write_text(result.stdout)
    if result.returncode:
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    print(script+': PASS')
r=json.loads((ROOT/'verification/RESULTS.json').read_text())
print(json.dumps({'status':r['status'],'variables':r['circuit']['variables'],
                  'degree':r['degree']['exact_degree'],
                  'operations':r['circuit']['operation_total'],
                  'fixed_leaves':r['circuit']['fixed_leaves']}))
compact=ROOT/'optional_compact'/'reproduce.py'
if not compact.is_file():
    raise FileNotFoundError('The complete delivery includes optional_compact/reproduce.py')
result=subprocess.run([sys.executable,str(compact)],cwd=ROOT,
                      text=True,capture_output=True)
(ROOT/'verification'/'compact_reproduction.txt').write_text(result.stdout)
print(result.stdout,end='')
if result.returncode:
    sys.stderr.write(result.stderr)
    raise SystemExit(result.returncode)
print('Both complete fixed instances: PASS')
