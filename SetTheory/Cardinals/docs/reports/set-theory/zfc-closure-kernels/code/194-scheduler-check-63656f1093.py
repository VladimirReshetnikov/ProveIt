#!/usr/bin/env python3
"""Read-only source and regeneration checks for the shared-basis patch."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    record = json.loads((HERE / 'integration_metrics.json').read_text())
    rev = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=repo,
                         capture_output=True, text=True, check=True).stdout.strip()
    if rev != record['baseline_commit']:
        raise RuntimeError('Reconcile against this revision before proceeding: ' + rev)
    for row in record['files']:
        path = repo / row['path']
        expected = row['before_sha256']
        if expected is None:
            if path.exists():
                raise RuntimeError('Expected a new path: ' + str(path))
        elif sha(path.read_bytes()) != expected:
            raise RuntimeError('Baseline source changed: ' + str(path))
        proposal = HERE / 'overlay' / row['path']
        if sha(proposal.read_bytes()) != row['after_sha256']:
            raise RuntimeError('Proposal source changed: ' + str(proposal))
    subprocess.run(['git', 'apply', '--check', str(HERE / 'shared_basis.patch')],
                   cwd=repo, check=True)
    producer = HERE / 'overlay/Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py'
    with tempfile.TemporaryDirectory(prefix='shared-basis-check-') as tmp:
        subprocess.run([sys.executable, '-B', str(producer), '--out', tmp], check=True)
        subprocess.run([sys.executable, '-B', str(producer), '--out', tmp, '--check'], check=True)
        for name in ['DominatedImplication.lean', 'DomRho8.lean', 'Lukasiewicz.lean']:
            generated = Path(tmp) / 'BusyBeaver/ZFC' / name
            proposed = HERE / 'overlay/Computability/BusyBeaver/Lean/BusyBeaver/ZFC' / name
            if generated.read_bytes() != proposed.read_bytes():
                raise RuntimeError('Generated proposal mismatch: ' + name)
    print('PASS: pinned baseline, patch applicability, and all three reproduced sources.')

if __name__ == '__main__':
    main()
