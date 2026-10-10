#!/usr/bin/env python3
"""Regenerate exact certificates and optionally independent numeric diagnostics.

Run normally (not with Python -O). Requires only the standard library unless
--numeric is passed. No network access or repository modification is performed.
"""
from __future__ import annotations
from argparse import ArgumentParser
from datetime import datetime,timezone
from pathlib import Path
import importlib.metadata
import json
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent.parent

def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--numeric',action='store_true')
    args=p.parse_args()
    if not __debug__:raise RuntimeError('Run without -O: assertions are part of the checks.')
    commands=[['verification/certify.py'],['verification/certify_minimum.py'],
              ['verification/test_algebra.py'],['verification/test_integration.py']]
    if args.numeric:
        commands += [['verification/numerical_checks.py',mode,'--dps','45']
                     for mode in ['identity','roots','minimum','fold']]
    results=[];log=[]
    for command in commands:
        started=time.monotonic()
        proc=subprocess.run([sys.executable,*command],cwd=ROOT,text=True,
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=False)
        elapsed=time.monotonic()-started
        printable='python '+' '.join(command)
        log.append('$ '+printable+'\n'+proc.stdout+'\n')
        results.append({'command':printable,'return_code':proc.returncode,
                        'elapsed_seconds':round(elapsed,6),
                        'kind':'non-interval numerical diagnostic' if 'numerical_checks.py' in command[0]
                               else 'exact-arithmetic or integration regression replay'})
        print(('PASS' if proc.returncode==0 else 'FAIL')+': '+printable,flush=True)
        if proc.returncode:
            (ROOT/'verification/validation.log').write_text('\n'.join(log))
            raise RuntimeError('A validation command failed; see validation.log')
    data={'completed_utc':datetime.now(timezone.utc).isoformat(),
          'python':platform.python_version(),'mpmath':importlib.metadata.version('mpmath') if args.numeric else None,
          'all_commands_passed':True,'results':results,
          'evidence_note':'Exact certificate replay is distinct from ordinary analytic proof. Numerical residuals and locations are not interval certificates.',
          'scope_note':'Neither proof-assistant formalization nor a full repository manuscript build is performed by this driver.'}
    (ROOT/'verification/validation.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'verification/validation.log').write_text('\n'.join(log))

if __name__=='__main__':main()
