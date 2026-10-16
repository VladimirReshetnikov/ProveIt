#!/usr/bin/env python3
"""Offline quick verification; does not rerun the expensive search grids.

Python 3.10+ standard library only. Run without -O/-OO. No network or formal
compiler is invoked. Temporary generated outputs are removed after comparison.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='optional JSON report path')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Run without -O/-OO: the research checkers use assertions.')
    started = time.monotonic()
    records = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')

    def run(label, argv, cwd=ROOT):
        result = subprocess.run([sys.executable, '-B', *map(str, argv)], cwd=cwd,
                                env=env, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(f'FAILED: {label}')
        records.append({'check': label, 'exit_code': result.returncode,
                        'stdout': result.stdout, 'stderr': result.stderr})
        print(f'PASS: {label}', flush=True)

    run('kernel, fixed theory, and integration tests',
        ['-m', 'unittest', 'discover', '-s', 'code', '-p', 'test_*.py', '-v'])
    with tempfile.TemporaryDirectory(prefix='zfc-quick-replay-') as tmp:
        temp = Path(tmp)
        stream_output = temp / 'streams'
        run('independent stream-table suite',
            [ROOT/'code/check_stream_renaming.py', '--output', stream_output])
        assert (stream_output/'stream_transducers.json').read_bytes() == (
            ROOT/'results/stream_transducers.json').read_bytes()
        machine = ROOT/'experiments/machine_audit'
        run('31,878 exact-quotient witnesses', ['quotient_certificate.py', '--check'], machine)
        run('253 table and state-map regeneration',
            ['vendor/busy-beaver/ZF/m253/tools/generate_candidate.py', '--check'], machine)
        run('6,460 instruction-site regeneration',
            ['vendor/busy-beaver/ZF/m253/tools/gen_sites253.py', '--check'], machine)
        compiler = ROOT/'experiments/compiler'
        replay = temp/'compiler'
        run('fixed 268-state compiler winner replay',
            ['rho8_grid.py', '--output', replay, '--seeds', '1', '--start-seed', '341',
             '--exponents', '4', '--modes', 'legacy', '--perms', '0'], compiler)
        files = ['candidate.dag.json', 'candidate.named.tm', 'candidate.tm', 'grammar.json',
                 'labels.json', 'reference.dag.json', 'rm_certificate.json', 'source_semantics.json']
        comparisons = {}
        for name in files:
            comparisons[name] = ((replay/name).read_bytes() ==
                                 (compiler/'results/rho8_grid_results'/name).read_bytes())
        assert all(comparisons.values()), comparisons
        verify = compiler/'vendor/source19/verify_schema_rm_certificate.py'
        run('grid 4,533-pair independent register certificate',
            [verify, '--prior-machine-dir', compiler/'vendor/prior',
             '--reference', replay/'reference.dag.json', '--candidate', replay/'candidate.dag.json',
             '--certificate', replay/'rm_certificate.json'], compiler)
        run('rotation 4,533-pair independent register certificate',
            [verify, '--prior-machine-dir', compiler/'vendor/prior',
             '--reference', compiler/'results/rho8_grid_results/candidate.dag.json',
             '--candidate', compiler/'results/rotation_extended/candidate.dag.json',
             '--certificate', compiler/'results/rotation_extended/rm_certificate.json'], compiler)
        stream_summary = json.loads((stream_output/'stream_renaming_results.json').read_text())
    report = {
        'status': 'all quick checks passed',
        'scope': 'finite checks and supplied certificate replay; no local Coq/Lean rebuild',
        'new_sub253_machine': False,
        'full_search_grids_rerun': False,
        'compiler_eight_artifacts_byte_identical': comparisons,
        'stream_summary': stream_summary,
        'checks': records,
        'seconds': round(time.monotonic() - started, 3),
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'scope', 'seconds')}, indent=2))


if __name__ == '__main__':
    main()
