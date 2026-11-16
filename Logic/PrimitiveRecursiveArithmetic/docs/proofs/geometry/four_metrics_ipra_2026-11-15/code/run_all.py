#!/usr/bin/env python3
"""Replay the complete exact certificate suite.

Usage:
  python3 code/run_all.py             # Python standard library only
  python3 -O code/run_all.py --sympy   # also run independent SymPy checks

Each checker runs in a fresh sequential subprocess, so the off-shell
six-variable configuration cannot affect the other five-variable runs.
The parent's Python optimization setting is propagated to every child.
Any nonzero exit code aborts the suite and records FAIL. Child logs and
the runner summary are written only beneath certificates/.
"""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sympy', action='store_true',
                        help='also run the independent SymPy engine and tensor comparison')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    code = root/'code'
    cert = root/'certificates'
    cert.mkdir(parents=True,exist_ok=True)
    jobs = [
        ('verify_stdlib.py','stdlib_run.log'),
        ('verify_offshell.py','offshell_run.log'),
        ('verify_ingoing.py','ingoing_run.log'),
        ('verify_stereographic.py','stereographic_run.log'),
        ('verify_curvature.py','curvature_run.log'),
        ('check_controls.py','negative_controls.log'),
    ]
    if args.sympy:
        jobs += [('verify_sympy.py','sympy_run.log'),
                 ('compare_engines.py','engine_comparison.log')]
    summary = {'status':'RUNNING','python_version':sys.version.split()[0],
               'optimization_level':sys.flags.optimize,
               'sympy_requested':args.sympy,'runs':[]}
    destination = cert/'suite_results.json'
    optimize = ['-'+'O'*sys.flags.optimize] if sys.flags.optimize else []
    for script,log in jobs:
        start = time.monotonic()
        result = subprocess.run([sys.executable,*optimize,str(code/script)],
                                cwd=root,stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT,text=True,check=False)
        (cert/log).write_text(result.stdout)
        item = {'script':script,'log':log,'exit_code':result.returncode,
                'seconds':round(time.monotonic()-start,3)}
        summary['runs'].append(item)
        if result.returncode:
            summary['status']='FAIL'
            destination.write_text(json.dumps(summary,indent=2)+'\n')
            print(result.stdout,end='')
            print(f'FAIL: {script} exited {result.returncode}; see certificates/{log}',file=sys.stderr)
            return result.returncode if result.returncode>0 else 1
        print(f'PASS: {script} ({item["seconds"]:.3f}s)',flush=True)
    summary['status']='PASS'
    destination.write_text(json.dumps(summary,indent=2)+'\n')
    print(f'PASS: all {len(jobs)} certificate programs; certificates/suite_results.json',flush=True)
    return 0


if __name__=='__main__':
    raise SystemExit(main())
