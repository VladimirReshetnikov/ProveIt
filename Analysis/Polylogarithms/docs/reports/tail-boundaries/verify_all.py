#!/usr/bin/env python3
"""Replay all exact certificates and the routine numerical diagnostics.

--full additionally rebuilds the independent C++ certificate and reruns the
slower independent Stieltjes finite-part quadratures. Complete recorded
results for both are supplied even when the default command is used.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full',action='store_true')
    args=parser.parse_args()
    calls=[
      ('bilinear and shifted kernels',['verification/kernels/verify_kernels.py']),
      ('Mellin and polylogarithm identities',['verification/mellin/verify_mellin_polylog.py']),
      ('Stieltjes coefficient and endpoint identities',['verification/stieltjes/code/verify_stieltjes_edge.py','--mode','all' if args.full else 'exact']),
      ('complete tail reconstruction certificates',['verification/tails/run_tail_checks.py']+(['--full'] if args.full else [])),
    ]
    checks=[]
    for name,command in calls:
        print(f'\nRunning {name} ...',flush=True)
        started=time.perf_counter()
        subprocess.run([sys.executable,'-B',*command],cwd=ROOT,check=True)
        checks.append({'check':name,'passed':True,'elapsed_seconds_diagnostic':round(time.perf_counter()-started,3)})
    result={'all_passed':True,'full_replay':args.full,'checks':checks,
            'note':'Numerical residuals are arbitrary-precision diagnostics, not interval certificates. Written analytic proofs establish the infinite parameter ranges.'}
    name='verification/replay_full.json' if args.full else 'verification/replay.json'
    (ROOT/name).write_text(json.dumps(result,indent=2)+'\n')
    print('\nAll requested verifications passed.',flush=True)


if __name__=='__main__':main()
