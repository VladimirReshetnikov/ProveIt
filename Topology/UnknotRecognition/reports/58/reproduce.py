#!/usr/bin/env python3
"""Reproduce individual research gates without replacing the published results."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
FAST = ROOT / 'code' / 'fast'
OUT = ROOT / 'local_results'


def call(args, cwd=FAST):
    print('Running:', ' '.join(str(x) for x in args), flush=True)
    subprocess.run([str(x) for x in args], cwd=cwd, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('verify', help='Verify every file in the delivered SHA-256 manifest')
    commands.add_parser('tests', help='Run the 148-method focused regression gate')
    audit = commands.add_parser('audit', help='Replay the frozen bounded geometric corpus')
    audit.add_argument('--fresh', action='store_true', help='Recompute Regina oracle answers too')
    bench = commands.add_parser('bench', help='Rerun paired measurements (several minutes)')
    bench.add_argument('--quick', action='store_true', help='Use the driver smoke-sized family set')
    bench.add_argument('--rounds', type=int, default=5)
    bench.add_argument('--timeout', type=float, default=90)
    commands.add_parser('formulas', help='Check all recorded spectra against geometric family formulas')
    commands.add_parser('proofs', help='Replay the 52 retained benchmark certificates')
    commands.add_parser('figures', help='Regenerate figures, tables and CSV from the recorded JSON')
    commands.add_parser('article', help='Build a copy of the LaTeX article in local_results')
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    if args.command == 'verify':
        manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
        errors = []
        for record in manifest['files']:
            path = ROOT / record['path']
            if not path.is_file():
                errors.append(record['path'] + ': missing')
            elif hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
                errors.append(record['path'] + ': hash mismatch')
        print(json.dumps(dict(files=len(manifest['files']), errors=errors,
                              success=not errors), indent=2))
        raise SystemExit(bool(errors))
    if args.command == 'tests':
        call([sys.executable, FAST / 'topology_research/run_tests.py',
              '--output', OUT / 'tests'])
    elif args.command == 'audit':
        command = [sys.executable, FAST / 'topology_research/regina_audit.py', 'audit',
                   '--corpus', FAST / 'topology_research/data/regina_corpus.json',
                   '--output', OUT / ('regina_fresh.json' if args.fresh else 'regina_replay.json')]
        if args.fresh:
            command.append('--recheck-oracle')
        call(command)
    elif args.command == 'bench':
        command = [sys.executable, FAST / 'topology_research/benchmark.py',
                   '--output', OUT / 'benchmark-rerun.json', '--rounds', args.rounds,
                   '--seed', 2026100919, '--timeout', args.timeout, '--save-proofs']
        if args.quick:
            command.append('--quick')
        call(command)
    elif args.command == 'formulas':
        call([sys.executable, FAST / 'topology_research/check_benchmark_formulas.py',
              ROOT / 'results/benchmark-final.json', '--proofs',
              ROOT / 'results/benchmark-final-proofs', '--output',
              OUT / 'benchmark_formula_audit.json'])
    elif args.command == 'proofs':
        call([sys.executable, FAST / 'topology_research/replay_benchmark_proofs.py',
              '--benchmark', ROOT / 'results/benchmark-final.json', '--proofs',
              ROOT / 'results/benchmark-final-proofs', '--output',
              OUT / 'benchmark_proof_replay.json'])
    elif args.command == 'figures':
        call([sys.executable, ROOT / 'article/plot_results.py',
              ROOT / 'results/benchmark-final.json', '--output', OUT / 'figures'], cwd=ROOT)
    elif args.command == 'article':
        destination = OUT / 'article-build'
        shutil.copytree(ROOT / 'article', destination, dirs_exist_ok=True)
        call(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
              'article.tex'], cwd=destination)
        print('Built:', destination / 'article.pdf')


if __name__ == '__main__':
    main()
