"""Rebuild the exact propositional/completeness bridge source closure serially.

Usage: python check_propositional_bridge.py --repo PATH --lean /path/to/lean
The repository must contain the three supplied integration modules and the
seven pinned dependency modules. All objects and logs go to a fresh directory.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

UNITS = [
    ('Logic/FirstOrder/Lean', 'FirstOrder/Fol.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/Kalmar.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/TarskiCalculus.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/TarskiDerived.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/TarskiLeibniz.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/TarskiClean.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/TarskiComplete.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/Lukasiewicz.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/TarskiCompleteRows.lean'),
    ('Computability/BusyBeaver/Lean', 'BusyBeaver/ZFC/PrimitiveBottomAudit.lean'),
]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, default=Path(__file__).resolve().parent)
    p.add_argument('--lean', default='lean')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    repo = args.repo.resolve()
    if args.output is None:
        output = Path(tempfile.mkdtemp(prefix='zfc-propositional-'))
    else:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_PATH=str(output))
    version = subprocess.check_output([args.lean, '--version'], text=True, env=env).strip()
    records = []
    for srcroot, module in UNITS:
        source = repo / srcroot / module
        data = source.read_bytes()
        if re.search(rb'\b(sorry|admit|native_decide)\b|^\s*axiom\s', data, re.M):
            raise SystemExit(f'Unpermitted admission/native declaration in {source}')
        obj = output / Path(module).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        run = subprocess.run([args.lean, '-o', str(obj), module],
                             cwd=repo / srcroot, env=env, capture_output=True, text=True)
        log = obj.with_suffix('.log')
        log.write_text(run.stdout + run.stderr)
        record = dict(source=f'{srcroot}/{module}',
                      source_sha256=hashlib.sha256(data).hexdigest(),
                      source_git_sha1=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),
                      returncode=run.returncode, log=str(log.relative_to(output)),
                      compiler_output=run.stdout + run.stderr)
        records.append(record)
        print(f'{module}: exit {run.returncode}', flush=True)
        if run.returncode or 'sorryAx' in run.stdout or "declaration uses 'sorry'" in run.stdout:
            print(run.stdout + run.stderr)
            raise SystemExit(run.returncode or 1)
    evidence = dict(lean_version=version,
                    proveit_pin='4747142d5d15213eb711bdadfa3cc7e769fcb7a7',
                    upstream_pin='297ab8df7e5de329605c3875b4934643b371a5e3',
                    source_modules=len(records), modules=records)
    (output / 'verification.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(f'All {len(records)} source modules checked. Evidence: {output}', flush=True)


if __name__ == '__main__':
    main()
