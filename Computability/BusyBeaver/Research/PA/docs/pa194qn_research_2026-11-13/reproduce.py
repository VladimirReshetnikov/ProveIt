#!/usr/bin/env python3
"""Rebuild and verify PA194QN in a fresh temporary copy of this packet."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile


def main():
    assert __debug__ and not sys.flags.optimize, 'Run without -O.'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true',
                    help='Skip generic and independent full physical symbolic checks.')
    ap.add_argument('--work', type=Path, help='New nonexistent directory for replay evidence.')
    args = ap.parse_args()
    original = Path(__file__).resolve().parent
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        work = args.work.resolve()
    else:
        work = Path(tempfile.mkdtemp(prefix='pa194qn-replay-'))
    package = work / 'packet'
    shutil.copytree(original, package,
                    ignore=shutil.ignore_patterns('__pycache__', '*.pyc', '*.aux', '*.log',
                                                 '*.out', '*.toc', '*.pdf'))
    logs = work / 'logs'
    logs.mkdir()
    commands = [
        ('build', ['construction/build.py'] + (['--quick'] if args.quick else [])),
        ('commands', ['verification/check_commands.py']),
        ('exchange', ['verification/exchange_certificate.py']),
        ('source', ['verification/audit_source.py', '--candidate', 'machine',
                    '--output', 'evidence/source_review.json']),
    ]
    if not args.quick:
        commands.append(('independent', ['verification/check_literal.py', 'machine',
                                        '--output', 'evidence/independent']))
    commands.append(('novelty', ['comparison/check_novelty.py', 'machine/machine.tm',
                                '--output', 'evidence/novelty.json']))
    for name, command in commands:
        print('Checking ' + name + '...', flush=True)
        with (logs / (name + '.log')).open('w') as stream:
            result = subprocess.run([sys.executable, '-B'] + command, cwd=package,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f'{name} failed; inspect {logs / (name + ".log")}')
    for name in ['machine.tm', 'machine.native.tm', 'raw.native.tm', 'labels.json',
                 'source.json', 'sites.json', 'instructions.json', 'nodes.json', 'folds.json']:
        assert (package / 'machine' / name).read_bytes() == (original / 'machine' / name).read_bytes(), name
    novelty = json.loads((package / 'evidence/novelty.json').read_text())
    assert novelty['novel'] and not novelty['matches']
    receipt = dict(status='PASS', family='PA194QN', full_physical_replay=not args.quick,
                   dense_sha256=hashlib.sha256((package / 'machine/machine.tm').read_bytes()).hexdigest(),
                   exact_regenerated_files=9, checks=[name for name, command in commands],
                   corpus_classes=novelty['corpus_graph_classes'], graph_matches=[],
                   proof_assistant_kernel_checked=False, evidence_directory=str(work))
    (work / 'REPLAY_RESULT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
