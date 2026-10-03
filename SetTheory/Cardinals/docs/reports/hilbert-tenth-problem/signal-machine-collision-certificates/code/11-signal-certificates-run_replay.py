#!/usr/bin/env python3
"""Replay all exact suites in isolation and compare the expected receipts."""
from pathlib import Path
import argparse, json, shutil, subprocess, sys, tempfile

if not __debug__:
    raise SystemExit('Assertions are required: do not run Python with -O.')
ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=ROOT/'replay-output')
args=parser.parse_args()
suites=[('signal_geometry.py','signal_geometry_receipt.json'),
        ('signal_sparse.py','signal_sparse_receipt.json'),
        ('verify_additional.py','additional_verification_receipt.json'),
        ('verify_examples.py','worked_examples_receipt.json')]
args.output.mkdir(parents=True,exist_ok=True)
summary=[]
with tempfile.TemporaryDirectory(prefix='signal-diophantine-') as tmp:
    work=Path(tmp)
    for source in (ROOT/'scripts').glob('*.py'):
        shutil.copy2(source,work/source.name)
    for script,receipt in suites:
        print(f'Running {script}',flush=True)
        run=subprocess.run([sys.executable,str(work/script)],cwd=work,text=True,capture_output=True)
        if run.returncode:
            sys.stdout.write(run.stdout);sys.stderr.write(run.stderr)
            raise SystemExit(f'{script} failed with status {run.returncode}')
        fresh=json.loads((work/receipt).read_text())
        expected=json.loads((ROOT/'expected_receipts'/receipt).read_text())
        if fresh!=expected:
            raise SystemExit(f'Receipt mismatch for {script}:\nexpected={expected}\nactual={fresh}')
        shutil.copy2(work/receipt,args.output/receipt)
        summary.append(dict(script=script,receipt=receipt,matched=True))
        print(f'  PASS: exact receipt matched',flush=True)
    # Replay-generated coefficient examples should also match the distributed data.
    for name in ['signal_geometry_examples.json','signal_sparse_examples.json']:
        assert json.loads((work/name).read_text())==json.loads((ROOT/'examples'/name).read_text()), name
    summary.append(dict(coefficient_examples_matched=True))
result=dict(status='PASS',python=sys.version.split()[0],suites=summary)
(args.output/'replay_summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
