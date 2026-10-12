#!/usr/bin/env python3
"""Reproduce in a temporary copy without overwriting delivered measurements."""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmarks', action='store_true')
    parser.add_argument('--pdf', action='store_true', help='also rebuild using pdflatex')
    parser.add_argument('--output', type=Path, default=Path('reproduction'))
    args = parser.parse_args()
    if not __debug__:
        parser.error('audits require assertions; do not use python -O')
    root = Path(__file__).resolve().parent
    out = args.output.resolve()
    if out == root or root in out.parents and out.name in {'src','tests','data','article','integration'}:
        parser.error('output must not replace a delivered source or data directory')
    out.mkdir(parents=True, exist_ok=True)
    log = []
    with tempfile.TemporaryDirectory(prefix='private_cocore_reproduce_') as temp:
        work = Path(temp) / 'package'
        shutil.copytree(root, work, ignore=shutil.ignore_patterns(
            '__pycache__', '*.pyc', 'reproduction', '*.aux', '*.log', '*.out', '*.toc'))
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        env['PYTHONPATH'] = os.pathsep.join([str(work/'src'), str(work/'tests')])
        commands = [
            [sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
            [sys.executable, 'experiments/audit.py'],
            [sys.executable, 'experiments/domination_audit.py'],
            [sys.executable, 'experiments/replay_saved.py'],
        ]
        if args.benchmarks:
            commands.append([sys.executable, 'experiments/benchmark.py'])
        for command in commands:
            print('+', ' '.join(command), flush=True)
            completed = subprocess.run(command, cwd=work, env=env, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(completed.stdout, end='')
            log.append('+ ' + ' '.join(command) + '\n' + completed.stdout)
            (out/'run.txt').write_text('\n'.join(log), encoding='utf-8')
            if completed.returncode:
                return completed.returncode
        for name in ['exhaustive-audit.json','domination-audit.json'] + (
                ['benchmarks.json'] if args.benchmarks else []):
            shutil.copy2(work/'data'/name, out/name)
        if args.pdf:
            exe = shutil.which('pdflatex')
            if exe is None:
                print('pdflatex is required for --pdf', file=sys.stderr)
                return 2
            for _ in range(3):
                command = [exe, '-interaction=nonstopmode', '-halt-on-error',
                           'private_cocore_transport.tex']
                completed = subprocess.run(command, cwd=work/'article', env=env, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                log.append('+ ' + ' '.join(command) + '\n' + completed.stdout)
                (out/'run.txt').write_text('\n'.join(log), encoding='utf-8')
                if completed.returncode:
                    print(completed.stdout)
                    return completed.returncode
            shutil.copy2(work/'article/private_cocore_transport.pdf',out/'private_cocore_transport.pdf')
    print('PASS. Fresh results:', out)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
