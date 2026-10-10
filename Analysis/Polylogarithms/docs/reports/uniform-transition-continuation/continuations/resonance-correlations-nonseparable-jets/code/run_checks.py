#!/usr/bin/env python3
"""Replay exact checks and optional independent analytic diagnostics.

The default exact suite has no third-party dependencies. Analytic suites
use mpmath; resonance also uses SymPy. Herglotz's Bessel replay can be slow.
No floating-point comparison is used as a substitute for an analytic proof.
"""
from pathlib import Path
import argparse
import datetime as dt
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT/'code'
DATA = ROOT/'data'


def replay(script, *args):
    print('Running '+script+' ...', flush=True)
    start = time.monotonic()
    proc = subprocess.run([sys.executable, str(CODE/script), *map(str, args)],
                          cwd=ROOT, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)
    elapsed = time.monotonic()-start
    if proc.returncode:
        print(proc.stdout)
        raise SystemExit(proc.returncode)
    print('  passed in %.2f seconds' % elapsed, flush=True)
    return proc.stdout, elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', choices=['exact','resonance','gamma',
                                           'herglotz','all'], default='exact')
    args = parser.parse_args()
    suites = ['exact','resonance','gamma','herglotz'] if args.suite == 'all' else [args.suite]
    DATA.mkdir(exist_ok=True)
    runs = []
    for suite in suites:
        if suite == 'exact':
            stdout, elapsed = replay('verify_nonseparable_jets.py')
            result = json.loads(stdout)
            assert result['status'] == 'all assertions passed'
            (DATA/'nonseparable_jets_checks.json').write_text(
                json.dumps(result, indent=2)+'\n')
        elif suite == 'resonance':
            _, elapsed = replay('check_resonance.py')
        elif suite == 'gamma':
            _, t1 = replay('check_gamma_correlations.py')
            stdout, t2 = replay('gamma_correlation.py')
            # The module prints JSON objects, one per verification case.
            for line in stdout.splitlines():
                json.loads(line)
            (DATA/'gamma_correlation_verification.jsonl').write_text(stdout)
            elapsed = t1+t2
        else:
            _, elapsed = replay('check_herglotz.py', DATA/'herglotz_checks.json')
        runs.append({'suite':suite,'status':'passed','elapsed_seconds':elapsed})
    report = {'completed_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
              'python':sys.version,'runs':runs,
              'scope':'Exact finite algebra and non-interval analytic diagnostics.'}
    (DATA/('replay_'+args.suite+'.json')).write_text(json.dumps(report,indent=2)+'\n')
    print('Requested checks completed; data files updated.')


if __name__ == '__main__':
    main()

