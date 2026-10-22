#!/usr/bin/env python3
"""Rebuild and compare all delivered arithmetic artifacts using Python's stdlib.

Run from any working directory with Python 3. The generators run in a
temporary copy: verification never overwrites the delivered circuits.
This checks finite algebra, ledgers, and reproducibility, not the imported
compiler/Pell mathematics or the K215 halting theorem.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
STEPS=[
    'low_degree/build_systems.py',
    'low_degree/quartic32.py',
    'low_degree/integer_quartic62.py',
    'arithmetic/build_candidates.py',
]
OUTPUTS=[
    'low_degree/ordinary15_system61.json',
    'low_degree/retained16_system60.json',
    'low_degree/system_checks.json',
    'low_degree/quartic32.json',
    'low_degree/quartic32_checks.json',
    'low_degree/integer_quartic62.json',
    'low_degree/integer_quartic62_checks.json',
    'arithmetic/system13_78.json',
    'arithmetic/sos13_89.json',
    'arithmetic/polynomial13_84.json',
    'arithmetic/system13_lowweight79.json',
    'arithmetic/sos13_lowweight90.json',
    'arithmetic/polynomial13_lowweight85.json',
    'arithmetic/product14_75.json',
    'arithmetic/outer14_73.json',
    'arithmetic/amalgam14_system67.json',
    'arithmetic/amalgam14_sos81.json',
    'arithmetic/amalgam14_product76.json',
    'arithmetic/candidate_receipt.json',
]

def main():
    missing=[name for name in STEPS+OUTPUTS if not (ROOT/name).is_file()]
    if missing:
        raise RuntimeError('Missing packaged files: '+', '.join(missing))
    env=dict(os.environ)
    env.pop('PYTHONOPTIMIZE',None)
    env['PYTHONDONTWRITEBYTECODE']='1'
    with tempfile.TemporaryDirectory(prefix='con-zfc-arithmetic-') as tmp:
        work=Path(tmp)
        for name in ('arithmetic','low_degree'):
            shutil.copytree(ROOT/name,work/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        for step in STEPS:
            result=subprocess.run([sys.executable,str(work/step)],cwd=work,
                                  env=env,text=True,capture_output=True)
            if result.returncode:
                raise RuntimeError(step+' failed:\n'+result.stdout+result.stderr)
            print('PASS '+step)
        mismatches=[]
        digests={}
        for name in OUTPUTS:
            expected=(ROOT/name).read_bytes()
            actual=(work/name).read_bytes()
            if actual!=expected:mismatches.append(name)
            digests[name]=hashlib.sha256(actual).hexdigest()
        if mismatches:
            raise RuntimeError('Reproduction mismatch: '+', '.join(mismatches))
        receipt=json.loads((work/'arithmetic/candidate_receipt.json').read_text())
        p84=receipt['packets']['polynomial13_84']
        p85=receipt['packets']['polynomial13_lowweight85']
        if (p84['variables'],p84['ledger']['operations'],p84['degree_diagnostics'][0]['degrees'])!=(13,84,[571]):
            raise RuntimeError('13-variable 84-operation ledger mismatch')
        if (p85['variables'],p85['ledger']['operations'],p85['degree_diagnostics'][0]['degrees'])!=(13,85,[515]):
            raise RuntimeError('13-variable 85-operation ledger mismatch')
        q32=json.loads((work/'low_degree/quartic32_checks.json').read_text())
        q62=json.loads((work/'low_degree/integer_quartic62_checks.json').read_text())
        if (q32['positive_variables'],q32['equations'],q32['sum_of_squares_degree'])!=(32,23,4):
            raise RuntimeError('32-positive-variable quartic dimensions mismatch')
        if (q62['integer_variables'],q62['quadratic_equations'],q62['quartic_degree'])!=(62,33,4):
            raise RuntimeError('62-integer-variable quartic dimensions mismatch')
        print('PASS: all '+str(len(OUTPUTS))+' generated JSON artifacts reproduce byte for byte.')
        print('PASS: 13-variable products (84 ops, degree 571; 85 ops, degree 515); '
              '32-positive-variable and 62-integer-variable quartics.')
        print('Scope: finite arithmetic and reproducibility checks; no proof-assistant build or consistency proof.')
    return 0

if __name__=='__main__':
    try:
        raise SystemExit(main())
    except (OSError,RuntimeError,ValueError,KeyError) as exc:
        print('FAIL: '+str(exc),file=sys.stderr)
        raise SystemExit(1)
