#!/usr/bin/env python3
"""Run the numerical replay, preserving immutable references separately."""
import argparse
import importlib.metadata
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
MARKER = '.galled-density-replay-output'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='Only rows through 27, all public integer references, and the scalar amplitude diagnostic')
    parser.add_argument('--skip-amplitude', action='store_true', help='Omit the optional independent scalar amplitude diagnostic')
    parser.add_argument('--output-dir', type=Path, help='Output folder; default: results/regenerated (or results/regenerated-quick)')
    args = parser.parse_args()
    versions = {name: importlib.metadata.version(name) for name in ('mpmath', 'sympy')}
    out = args.output_dir or ROOT/'results'/('regenerated-quick' if args.quick else 'regenerated')
    if out.is_symlink():
        parser.error('the output directory may not be a symlink')
    out = out.resolve()
    for protected in (ROOT/'code', ROOT/'data', ROOT/'results/expected'):
        if out == protected or out in protected.parents or protected in out.parents:
            parser.error('output directory overlaps a protected input/source directory')
    if out.exists():
        if not out.is_dir():
            parser.error('output path is not a directory')
        if any(out.iterdir()):
            if not (out/MARKER).is_file() or (out/MARKER).read_text() != 'generated-only\n':
                parser.error('refusing to clear an unmarked nonempty output directory; choose a fresh folder')
            shutil.rmtree(out)
    out.mkdir(parents=True, exist_ok=True)
    (out/MARKER).write_text('generated-only\n')
    (out/'stability').mkdir()
    started = time.perf_counter()
    runtime = {'python': platform.python_version(), 'implementation': platform.python_implementation(),
               'platform': platform.system(), 'machine': platform.machine(), 'dependencies': versions,
               'mode': 'quick' if args.quick else 'full', 'stages': [],
               'precision': {'constants': 80, 'density': 55, 'stability': [80, 60], 'amplitude': 85},
               'status': 'running'}

    def save_runtime():
        runtime['total_seconds'] = round(time.perf_counter()-started, 3)
        (out/'runtime.json').write_text(json.dumps(runtime, indent=2)+'\n')

    def run(label, script, options, log):
        print(label+' ...', flush=True)
        t = time.perf_counter()
        with (out/log).open('w') as stream:
            result = subprocess.run([sys.executable, str(ROOT/'code'/script), *map(str, options)],
                                    stdout=stream, stderr=subprocess.STDOUT, cwd=ROOT)
        elapsed = round(time.perf_counter()-t, 3)
        runtime['stages'].append({'name': label, 'script': script, 'seconds': elapsed,
                                  'exit_code': result.returncode, 'log': log})
        save_runtime()
        if result.returncode:
            runtime['status'] = 'failed'
            save_runtime()
            print((out/log).read_text(), file=sys.stderr)
            raise SystemExit(result.returncode)
        print(f'  finished in {elapsed:.3f} s', flush=True)

    rows = out/'independent-rows.json'
    run('Exact integer rows', 'independent_rows.py',
        ['--max-n', 27 if args.quick else 160, '--output', rows], 'rows.log')
    if not args.quick:
        run('Constants: cutoff 160, 80 digits', 'derive.py',
            ['--rows', rows, '--output', out/'constants.json', '--row-limit', 160, '--dps', 80], 'numerics.txt')
        run('Stability: cutoff 120, 80 digits', 'derive.py',
            ['--rows', rows, '--output', out/'stability/cutoff120-dps80.json', '--row-limit', 120, '--dps', 80], 'stability/cutoff120-dps80.log')
        run('Stability: cutoff 160, 60 digits', 'derive.py',
            ['--rows', rows, '--output', out/'stability/cutoff160-dps60.json', '--row-limit', 160, '--dps', 60], 'stability/cutoff160-dps60.log')
        run('Density checks: 55 digits', 'density_checks.py',
            ['--rows', rows, '--output', out/'density-checks.json', '--dps', 55], 'density-numerics.txt')
    if not args.skip_amplitude:
        run('Independent scalar amplitude: 85 digits', 'check_amplitude.py',
            ['--reference', ROOT/'data/oeis-reference.json', '--output', out/'amplitude-check.json', '--dps', 85], 'amplitude.log')
    options = ['--output-dir', out]
    if args.quick:
        options.append('--quick')
    if args.skip_amplitude:
        options.append('--skip-amplitude')
    run('Verify exact terms and numerical tolerances', 'verify_results.py', options, 'verification.log')
    runtime['status'] = 'passed'
    save_runtime()
    print(f"PASS: {runtime['mode']} replay in {runtime['total_seconds']:.3f} s", flush=True)
    print('Results: '+str(out), flush=True)
    print('Numerical stability is not an interval certificate.', flush=True)


if __name__ == '__main__':
    main()
