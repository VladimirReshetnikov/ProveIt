#!/usr/bin/env python3
"""Portable finite corroboration; the analytic proof is in article/."""
import sys
if sys.flags.optimize or not __debug__:
    raise SystemExit('Verification requires assertions; do not use Python -O.')
import argparse, hashlib, json, shutil, subprocess
from pathlib import Path
import mpmath as mp
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,default=ROOT/'verification-output');args=ap.parse_args()
out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
source=ROOT/'article'/'ballot-asymptotics.tex'
approval=json.loads((ROOT/'verification'/'receipts'/'approval.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest()==approval['source_sha256'], 'The mathematical source differs from the reviewed source.'
deriv=ROOT/'verification'/'derivations'
for name,digest in approval['executed_derivation_sources'].items():
    assert hashlib.sha256((deriv/name).read_bytes()).hexdigest()==digest, f'Derivation source changed: {name}'
subprocess.run([sys.executable,str(ROOT/'verification'/'check.py'),'--source-dir',str(deriv),'--output-dir',str(out/'exact')],check=True,stdout=(out/'exact-check.stdout').open('w'))
exact=json.loads((out/'exact'/'verification.json').read_text());assert exact['status']=='PASS'
producers=out/'producers';producers.mkdir(exist_ok=True)
for name in ['verify_ballot_large_dp.py','verify_ballot_numerical_derivatives.py']:
    shutil.copy2(deriv/name,producers/name)
    subprocess.run([sys.executable,str(producers/name)],check=True,stdout=(out/(name+'.stdout')).open('w'))
dp=json.loads((producers/'verify_ballot_large_dp.json').read_text());assert len(dp['reports'])==2
byq={r['q']:r for r in dp['reports']}
assert byq[4]['all_diagonal_terms'][10]=='159752979289765273698'
assert byq[5]['all_diagonal_terms'][20]=='20583327745215005844288257113206932906760798477397608945484080000'
mp.mp.dps=60
for row in dp['reports']:
    assert row['max_n']>=30
    assert abs(mp.mpf(row['diagnostics'][-1]['n_times_leading_relative_error'])-mp.mpf(row['c1']))<mp.mpf('.02')
auto=json.loads((producers/'verify_ballot_numerical_derivatives.json').read_text());assert {r['q'] for r in auto}=={4,5}
for row in auto:
    assert row['precision_decimal_digits']>=50
    assert mp.mpf(row['absolute_discrepancy'])<mp.mpf('1e-40')
receipt={'status':'PASS','mathematical_source_sha256':approval['source_sha256'],'scope':'Finite exact and numerical corroboration, not machine verification of the asymptotic proof','exact_checker':exact,'independent_dp_max_n':30,'independent_automatic_derivative_discrepancies':{str(r['q']):r['absolute_discrepancy'] for r in auto}}
(out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: reviewed source, exact identities, n<=30 independent DP, and automatic derivative checks')
