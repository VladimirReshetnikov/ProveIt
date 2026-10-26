#!/usr/bin/env python3
"""Replay focused proofs after `lake update` and obtaining Mathlib dependencies.

This does not apply production patches or claim to build upstream ProveIt.
"""
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / '.checks'
FILES = ['RealizerPrimrecBridge.lean', 'GenericREAdapter.lean',
         'MinimalPellBootstrap.lean', 'GuardDischarge.lean']


def main():
    LOGS.mkdir(exist_ok=True)
    commands = [['lake', 'build', 'DiophantineConsistency.ScalarPRCode']]
    commands.extend(['lake', 'env', 'lean', f] for f in FILES)
    records = []
    for index, command in enumerate(commands):
        start = time.monotonic()
        run = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        log = LOGS / f'{index:02d}-{Path(command[-1]).stem}.log'
        log.write_text(run.stdout + run.stderr)
        record = dict(command=command, exit_code=run.returncode,
                      seconds=round(time.monotonic()-start, 3), log=log.name)
        records.append(record)
        print(json.dumps(record))
        if run.returncode:
            (LOGS / 'results.json').write_text(json.dumps(records, indent=2)+'\n')
            raise SystemExit(run.returncode)
        if 'sorryAx' in run.stdout:
            raise SystemExit('Unexpected sorryAx in a successful check')
    (LOGS / 'results.json').write_text(json.dumps(records, indent=2)+'\n')
    print('Focused checks passed. Full upstream integration was not checked.')


if __name__ == '__main__':
    main()
