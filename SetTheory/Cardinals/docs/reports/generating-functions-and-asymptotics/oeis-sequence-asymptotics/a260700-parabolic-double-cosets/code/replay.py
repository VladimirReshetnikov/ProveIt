#!/usr/bin/env python3
"""Replay exact coefficients, finite enumeration and inverse diagnostics offline."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
import sympy as sp
import mpmath
ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
g=parser.add_mutually_exclusive_group()
g.add_argument('--quick',action='store_true');g.add_argument('--full',action='store_true')
parser.add_argument('--output-dir',type=Path,default=Path('replay-output'))
args=parser.parse_args();out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
N=400 if args.full else 40
start=time.monotonic()

def run(script,*arguments):
    cmd=[sys.executable,str(ROOT/'code'/script),*map(str,arguments)]
    with (out/(script+'.log')).open('w') as log:
        subprocess.run(cmd,check=True,stdout=log,stderr=subprocess.STDOUT,cwd=ROOT)
    print('PASS:',script,flush=True)

run('verify_manifest.py')
run('coefficients.py',4,'--output-dir',out)
expected=json.loads((ROOT/'data/coefficients-order4.json').read_text())
actual=json.loads((out/'coefficients-order4.json').read_text())
for name in ('D','U','B'):
    assert len(actual[name])==len(expected[name])==5
    for i,(a,b) in enumerate(zip(actual[name],expected[name])):
        pa,pb=sp.sympify(a),sp.sympify(b)
        assert not pa.atoms(sp.Float),(name,i,'floating atom')
        assert sp.expand(pa-pb)==0,(name,i)
run('validate.py',N,'--output-dir',out)
reference=json.loads((ROOT/'data/exact-values.json').read_text())
computed=json.loads((out/'exact-values.json').read_text())
for name in ('p','q'):
    assert computed[name]==reference[name][:N+1],name
checks=json.loads((out/'validation.json').read_text())
assert checks['exact_formula_matches_OEIS_through']==N
assert checks['brute_group_coset_counts']=={'1':1,'2':3,'3':19,'4':167,'5':1791}
assert checks['cycle_identity_checks']==259
run('inverse.py','--output-dir',out)
result={'status':'PASS','exact_formula_limit':N,'coefficient_order':4,
        'actual_group_coset_limit':5,'cycle_identity_checks':259,
        'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mpmath.__version__,
        'elapsed_seconds':round(time.monotonic()-start,3),
        'scope':'Exact algebra and numerical diagnostics; see the article for rigorous asymptotic remainders'}
(out/'replay-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
