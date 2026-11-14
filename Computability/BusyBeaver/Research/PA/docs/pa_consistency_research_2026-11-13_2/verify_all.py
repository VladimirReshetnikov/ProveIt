#!/usr/bin/env python3
"""Run the portable research checks; --full also recomputes abstract closures."""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Verification requires Python without -O or -OO.")

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true',
                        help='Recompute both abstract fixed points with g++ (C++17).')
    args = parser.parse_args()
    manifest = HERE / 'SHA256SUMS'
    checked_hashes = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            assert hashlib.sha256((HERE / name).read_bytes()).hexdigest() == digest, name
            checked_hashes += 1
        print(f'PASS: {checked_hashes} manifest hashes', flush=True)

    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    logs = HERE / 'verification_logs'
    logs.mkdir(exist_ok=True)
    results = {}

    def run(name, command):
        proc = subprocess.run(command, cwd=HERE, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / (name + '.txt')).write_text(proc.stdout)
        if proc.returncode:
            print(proc.stdout, file=sys.stderr)
            raise RuntimeError(f'{name} failed with exit status {proc.returncode}')
        results[name] = 'PASS'
        print('PASS: ' + name, flush=True)

    for name, script in [
        ('comparison', 'comparison/verify.py'),
        ('rotated196', 'rotated196/verify.py'),
        ('diagonal198', 'diagonal198/verify.py'),
        ('command_calculus_examples', 'command_reduction/halt_at_mp_checks.py'),
        ('command_source_examples', 'command_reduction/halt_at_mp_source_checks.py'),
        ('association_saved_witnesses', 'association_search/verify_saved.py'),
        ('engine_contracts_and_counterexample', 'engine_search/run_searches.py'),
    ]:
        run(name, [sys.executable, script])

    with tempfile.TemporaryDirectory(prefix='pa-consistency-verification-') as temp:
        temp = Path(temp)
        run('command_source_reconstruction', [
            sys.executable, 'command_reduction/reconstruct_halt_at_mp.py',
            '--program', 'rotated196/upstream/PA196/Program.lean',
            '--output', str(temp / 'reconstructed'),
        ])
        reconstructed = (temp / 'reconstructed/sites.json').read_bytes()
        assert reconstructed == (HERE / 'command_reduction/halt_at_mp_source_sites.json').read_bytes()
        assert json.loads(reconstructed) == json.loads((HERE / 'command_reduction/source_sites.json').read_text())

        # Bind both stored abstract graphs to the exact pinned source, using
        # the independent ordered-interval resolver from the command audit.
        sys.path.insert(0, str(HERE / 'command_reduction'))
        from reconstruct_halt_at_mp import parse_program, sites, PROGRAM_SHA256
        from halt_at_mp_source_checks import resolve
        raw = (HERE / 'rotated196/upstream/PA196/Program.lean').read_bytes()
        assert hashlib.sha256(raw).hexdigest() == PROGRAM_SHA256
        graph = resolve(sites(parse_program(raw)['node172']))
        assert [list(row) for row in graph] == json.loads((HERE / 'abstract_analysis/cfg.json').read_text())
        numeric = []
        for row in graph:
            if row[0] == 'inc': numeric.append((0, row[1], row[2], -1))
            elif row[0] == 'dec': numeric.append((1, row[1], row[2], row[3]))
            elif row[0] == 'jump': numeric.append((2, -1, row[1], -1))
            else:
                assert row == ('halt',)
                numeric.append((3, -1, -1, -1))
        lines = (HERE / 'abstract_analysis/cfg.txt').read_text().splitlines()
        assert int(lines[0]) == len(numeric) == 3812
        assert [tuple(map(int, line.split())) for line in lines[1:]] == numeric
        candidate_graph = resolve(json.loads(reconstructed))
        assert [list(row) for row in candidate_graph] == json.loads((HERE / 'command_reduction/source_cfg.json').read_text())
        results['stored_graphs_bound_to_pinned_source'] = 'PASS'
        print('PASS: stored_graphs_bound_to_pinned_source', flush=True)

        run('cache_flexible_source_variants', [sys.executable,
            'command_reduction/cache_flexible_variants.py',
            '--output', str(temp / 'cache-variants')])
        for name in ('results.json', 'two_decrement_test.sites.json',
                     'positive_consequent.sites.json'):
            assert (temp / 'cache-variants' / name).read_bytes() == (
                HERE / 'command_reduction/cache_flexible_variants' / name).read_bytes()

        if args.full:
            exe = temp / 'abstract-closure'
            run('compile_abstract_closure', ['g++', '-O3', '-std=c++17',
                'abstract_analysis/closure.cpp', '-o', str(exe)])
            for radix in (3, 4):
                receipt = temp / f'radix{radix}.json'
                run(f'abstract_radix{radix}', [str(exe),
                    'abstract_analysis/cfg.txt', str(radix), str(receipt)])
                expected = json.loads((HERE / f'abstract_analysis/radix{radix}.json').read_text())
                assert json.loads(receipt.read_text()) == expected

    summary = {
        'status': 'PASS',
        'components': results,
        'abstract_closures_recomputed': args.full,
        'target_below_196_achieved': False,
        'scope': ('Reconstruction, table/source comparison, inherited symbolic '
                  'primitive contracts, exact startup, and explicitly scoped '
                  'source checks. No new Lean build or PA biconditional is certified.'),
    }
    (HERE / 'verification_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
