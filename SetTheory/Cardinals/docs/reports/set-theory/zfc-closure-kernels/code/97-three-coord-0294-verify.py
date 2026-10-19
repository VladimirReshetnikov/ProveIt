#!/usr/bin/env python3
"""Portable finite replay. Discovery and unbounded searches are not run."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled; do not use Python -O')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    p.add_argument('--skip-hashes', action='store_true', help='For edited sources only')
    a = p.parse_args()
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-kernel-replay-'))
    work.mkdir(parents=True, exist_ok=True)
    checked = 0
    if not a.skip_hashes:
        for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
            digest, rel = line.split('  ', 1)
            path = ROOT / rel
            assert path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == digest, rel
            checked += 1
        print(f'PASS: {checked} delivered hashes.', flush=True)
    tasks = []
    def run(name, args, cwd=ROOT):
        result = subprocess.run([sys.executable, '-B', *map(str, args)], cwd=cwd,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (work / (name + '.log')).write_text(result.stdout)
        if result.returncode:
            print(result.stdout)
            raise RuntimeError(name + ' failed')
        tasks.append(name)
        print('PASS: ' + name, flush=True)
    f = ROOT / 'formalism'
    run('selective-equality', [f / 'selective_equality.py', '--output', work / 'formalism'])
    for module in ('fused_hull', 'fused_witnesses', 'frozen_selective_control'):
        expression = ('import sys,json;from pathlib import Path;'
                      f'sys.path.insert(0,{str(f)!r});import {module};'
                      f'print(json.dumps({module}.run(Path({str(work / module)!r})),indent=2))')
        run(module, ['-c', expression])
    run('three-function', [ROOT / 'three_function/three_function_sharing.py',
                           '--output', work / 'three-function'])
    run('independent-substitution-and-opcodes', [ROOT / 'verification/check_three_function_independent.py',
         '--formalism-results', work / 'formalism', '--three-results', work / 'three-function',
         '--output', work / 'independent-substitution.json'])
    grammar = work / 'grammar_search'
    shutil.copytree(ROOT / 'grammar_search', grammar)
    run('grammar-39-candidates', [grammar / 'verify_structural_candidates.py'], cwd=grammar)
    run('scanner-positive-control', [ROOT / 'transition_search/verify_scanner_control.py',
                                     ROOT / 'transition_search/results/scanner8-control.json'])
    result = dict(status='PASS_FINITE_RESEARCH_PACKAGE', delivered_hashes=checked,
                  tasks=tasks, binary_tm_below_245=False,
                  proof_status='Ordinary mathematical proof and finite checks; no new kernel endpoint',
                  output=str(work))
    (work / 'verification-summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
