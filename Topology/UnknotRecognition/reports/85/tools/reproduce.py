#!/usr/bin/env python3
"""Portable reproduction of the new contribution, using the pinned snapshot."""

import argparse
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / 'runtime' / 'fast'
sys.path.insert(0, str(FAST))


def smoke():
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
    from fastunknot.sector_blocks_verify import verify_block_ray_certificate
    records = []
    for path in sorted((ROOT / 'examples').glob('*.json')):
        item = json.loads(path.read_text())
        source, proof = item['triangulation'], item['certificate']
        schema = proof['schema']
        if schema == 'normal-cut-handlebodies-v1':
            checked = verify_normal_cut_handlebodies(source, item['coordinates'], proof)
        elif schema == 'parallelity-boundary-words-v1':
            checked = verify_parallelity_boundary_words(source, item['coordinates'], proof)
        elif schema == 'normal-sector-block-rays-v1':
            checked = verify_block_ray_certificate(source, proof)
        else:
            raise ValueError('unknown example schema: ' + schema)
        if not checked:
            raise AssertionError('certificate rejected: ' + path.name)
        records.append(dict(file=path.name, schema=schema, independently_verified=True))
    if not records:
        raise AssertionError('no example certificates found')
    print(json.dumps(records, indent=2))


def run(*arguments):
    subprocess.run([sys.executable, *map(str, arguments)], cwd=FAST, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('smoke', 'tests', 'audits', 'benchmarks', 'all'))
    args = parser.parse_args()
    selected = {'smoke', 'tests', 'audits', 'benchmarks'} if args.action == 'all' else {args.action}
    output = ROOT / 'reproduced'
    output.mkdir(exist_ok=True)
    if 'smoke' in selected:
        smoke()
    if 'tests' in selected:
        run('-m', 'unittest', '-v',
            'tests.test_core_handlebody', 'tests.test_normal_cut_handlebodies',
            'tests.test_parallelity_boundary_words', 'tests.test_sector_blocks')
    if 'audits' in selected:
        run('-m', 'marked_parallelity_research.audit_census',
            '--output', output / 'census-audit.json')
        run('-m', 'sector_block_research.audit', 'audit',
            '--output', output / 'sector-corpus-audit.json')
        run(ROOT / 'tools' / 'annular_absorption_diagnostic.py',
            '--unknot-root', ROOT / 'runtime',
            '--census-audit', output / 'census-audit.json',
            '--output', output / 'annular-absorption-diagnostic.json')
    if 'benchmarks' in selected:
        run('-m', 'normal_orbit_research.parallelity_boundary_words',
            '--output', output / 'boundary-words-benchmark.json')
        run('-m', 'marked_parallelity_research.benchmark_census', '--rounds', '5', '--capacity',
            '--output', output / 'census-benchmark.json')
        run('-m', 'sector_block_research.audit', 'benchmark', '--rounds', '3', '--max-balls', '5',
            '--output', output / 'sector-benchmark.json')


if __name__ == '__main__':
    main()
