#!/usr/bin/env python3
"""Reproduce selected research tasks without overwriting archived evidence."""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
FAST = ROOT/'code/fast'
OUT = ROOT/'reproduced'

def run(label, command, cwd=ROOT):
    OUT.mkdir(exist_ok=True)
    environment = os.environ.copy()
    paths = [str(FAST), str(FAST/'tests')]
    if environment.get('PYTHONPATH'):
        paths.append(environment['PYTHONPATH'])
    environment['PYTHONPATH'] = os.pathsep.join(paths)
    log = OUT/(label+'.log')
    print(f'Running {label}; log: {log}', flush=True)
    with log.open('w') as stream:
        process = subprocess.Popen(command, cwd=cwd, env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            stream.write(line)
            print(line, end='', flush=True)
        status = process.wait()
    if status:
        raise SystemExit(status)

def verify_manifest():
    entries = (ROOT/'MANIFEST.sha256').read_text().splitlines()
    failures = []
    for entry in entries:
        expected, name = entry.split('  ', 1)
        path = ROOT/name
        if not path.is_file():
            failures.append(name+': missing')
        elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(name+': changed')
    if failures:
        print('\n'.join(failures))
        raise SystemExit(1)
    print(f'All {len(entries)} archived payload hashes match.')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('task', choices=['tests','audit','regina','benchmark',
        'example','figures','paper','verify-manifest'])
    args = parser.parse_args()
    python = sys.executable
    research = FAST/'weighted_research'
    if args.task == 'tests':
        run('tests', [python,'-m','unittest','discover','-s',str(FAST/'tests'),'-v'])
    elif args.task == 'audit':
        run('kernel_audit', [python,str(research/'kernel_audit.py'),'audit',
            '--output',str(OUT/'kernel_audit.json')])
        run('checker_audit', [python,str(research/'checker_audit.py'),
            '--output',str(OUT/'weighted_checker_audit.json')])
    elif args.task == 'regina':
        run('normal_audit', [python,str(research/'normal_audit.py'),
            '--corpus',str(ROOT/'results/normal_audit_20261009_corpus.json'),
            '--output',str(OUT/'normal_audit.json')])
    elif args.task == 'benchmark':
        run('kernel_benchmark', [python,str(research/'kernel_audit.py'),'benchmark',
            '--output',str(OUT/'kernel_benchmark.json')])
        run('normal_benchmark', [python,str(research/'normal_benchmark.py'),
            '--output',str(OUT/'normal_benchmark.json')])
    elif args.task == 'example':
        run('example', [python,str(ROOT/'examples/run_example.py'),
            '--output-dir',str(OUT/'examples')])
    elif args.task == 'figures':
        run('figures', [python,str(ROOT/'article/make_figures.py'),
            '--results',str(ROOT/'results'),'--output-dir',str(OUT/'article')])
    elif args.task == 'paper':
        destination = OUT/'paper'
        destination.mkdir(parents=True, exist_ok=True)
        tex = 'weighted_normal_components.tex'
        if shutil.which('latexmk'):
            run('paper', ['latexmk','-pdf','-interaction=nonstopmode','-halt-on-error',
                '-outdir='+str(destination),tex], ROOT/'article')
        else:
            for number in range(3):
                run('paper_pass_'+str(number+1), ['pdflatex','-interaction=nonstopmode',
                    '-halt-on-error','-output-directory='+str(destination),tex], ROOT/'article')
    else:
        verify_manifest()

if __name__ == '__main__':
    main()
