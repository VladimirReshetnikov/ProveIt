#!/usr/bin/env python3
"""Exercise resource, input, and integrity checks under normal Python and -O."""
import argparse
from contextlib import redirect_stderr
from io import StringIO
import json
from pathlib import Path
from output_json import emit_json, prepare_output
import subprocess
import sys
import tempfile
import third_sector as ts
from numerics import compute


def worker():
    # Each must raise explicitly. An assertion would disappear under python -O.
    cases = [
        ('N upper cap', lambda: ts.check_exact(257, 1)),
        ('N lower cap', lambda: ts.check_exact(0, 1)),
        ('N type', lambda: ts.check_exact(24.0, 1)),
        ('N boolean', lambda: ts.check_exact(True, 1)),
        ('k upper cap', lambda: ts.check_exact(24, 81)),
        ('k lower cap', lambda: ts.check_exact(24, 0)),
        ('k boolean', lambda: ts.check_exact(24, True)),
        ('bounded N cap', lambda: ts.bounded_counts(257, 1)),
        ('bounded k negative', lambda: ts.bounded_counts(12, -1)),
        ('bounded k upper cap', lambda: ts.bounded_counts(12, 81)),
        ('universal series cap', lambda: ts.universal_series(257)),
        ('rooted internal cap', lambda: ts.rooted_counts(513)),
        ('rooted negative', lambda: ts.rooted_counts(-1)),
        ('literal cap', lambda: ts.check_literal_trees(13)),
        ('literal lower cap', lambda: ts.check_literal_trees(0)),
        ('root tail cap', lambda: ts.check_root_tails(65, 6)),
        ('root tail leading term unreachable', lambda: ts.check_root_tails(31, 6)),
        ('root tail q negative', lambda: ts.check_root_tails(40, -1)),
        ('marked product cap', lambda: ts.marked_euler_product([0], 257)),
        ('Euler product wrong length', lambda: ts.euler_product([0], 2)),
        ('Euler negative exponent', lambda: ts.euler_product([0, -1], 1)),
        ('Euler boolean exponent', lambda: ts.euler_product([0, True], 1)),
        ('marked product negative exponent', lambda: ts.marked_euler_product([0, -1], 1)),
        ('Euler nonzero constant', lambda: ts.euler_product([1, 1], 1)),
        ('forest wrong coefficient length', lambda: ts.root_forest_cycle([0], 2)),
        ('unequal multiplication lengths', lambda: ts.mul([1], [1, 2])),
        ('empty multiplication', lambda: ts.mul([], [])),
        ('unequal addition lengths', lambda: ts.add([1], [1, 2])),
        ('empty product', lambda: ts.times()),
        ('negative shift', lambda: ts.shift([1], -1)),
        ('zero substitution degree', lambda: ts.substitute([1, 1], 0)),
        ('nonintegral coefficient division', lambda: ts.divide_exact([1], 2)),
        ('zero divisor', lambda: ts.divide_exact([1], 0)),
        ('integrity failure', lambda: ts.require(False, 'intentional failed integrity condition')),
        ('numeric tail upper cap', lambda: compute(481, 70)),
        ('numeric precision upper cap', lambda: compute(360, 201)),
        ('numeric precision lower cap', lambda: compute(360, 39)),
    ]
    passed = []
    for name, operation in cases:
        try:
            operation()
        except (ValueError, ArithmeticError):
            passed.append(name)
        else:
            raise RuntimeError(f'Guard failed: {name}')
    ts.require(ts.shift([1, 2], 2) == [0, 0], 'shift at truncation boundary')
    ts.require(ts.shift([1, 2], 20) == [0, 0], 'shift beyond truncation boundary')
    ts.require(ts.bounded_counts(5, 0) == [0, 1, 0, 0, 0, 0], 'zero degree boundary')
    ts.require(ts.bounded_counts(5, 1) == [0, 1, 1, 1, 1, 1], 'unary path boundary')
    ts.require(ts.rooted_counts(0) == [0], 'zero rooted cutoff')
    exclusive_checks = 0
    with tempfile.TemporaryDirectory() as directory:
        folder = Path(directory)
        for kind in ('regular_file', 'live_symlink', 'dangling_symlink'):
            output = folder / (kind + '.json')
            destination = folder / (kind + '-destination.json')
            sentinel = b'preserve this file\n'
            if kind == 'regular_file':
                output.write_bytes(sentinel)
            else:
                if kind == 'live_symlink':
                    destination.write_bytes(sentinel)
                output.symlink_to(destination)
            diagnostic = StringIO()
            try:
                with redirect_stderr(diagnostic):
                    # Deliberately skip prepare_output: this tests the final
                    # exclusive open against a name appearing after preflight.
                    emit_json(argparse.ArgumentParser(), {'status': 'pass'}, output)
            except SystemExit as error:
                ts.require(error.code == 2, 'Wrong exclusive-write failure code')
            else:
                raise RuntimeError('Final exclusive-write guard failed')
            ts.require('already exists' in diagnostic.getvalue(), 'Missing exclusive-write diagnostic')
            if kind == 'regular_file':
                ts.require(output.read_bytes() == sentinel, 'Final write changed existing content')
            else:
                ts.require(output.is_symlink() and output.readlink() == destination,
                           'Final write changed symlink')
                if kind == 'live_symlink':
                    ts.require(destination.read_bytes() == sentinel, 'Final write changed link destination')
                else:
                    ts.require(not destination.exists(), 'Final write followed dangling symlink')
            exclusive_checks += 1
    return {'status': 'pass', 'optimization_active': not __debug__,
            'rejected_inputs_and_integrity_checks': len(passed), 'check_names': passed,
            'valid_boundary_checks': 5, 'final_exclusive_write_checks': exclusive_checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    prepare_output(parser, args.output)
    if args.worker:
        result = worker()
    else:
        code = Path(__file__).resolve().parent
        results = []
        cli_cases = [('reproduce.py', '--n', '257'), ('reproduce.py', '--k', '81'),
                     ('reproduce.py', '--n', '-1'), ('reproduce.py', '--k', '0'),
                     ('reproduce.py', '--n', '1.5'), ('numerics.py', '--tail', '481'),
                     ('numerics.py', '--digits', '201')]
        for optimized in (False, True):
            prefix = [sys.executable, '-B'] + (['-O'] if optimized else [])
            process = subprocess.run(prefix + [str(code / 'check_guards.py'), '--worker'],
                                     capture_output=True, text=True, timeout=30, check=False)
            if process.returncode != 0:
                raise RuntimeError(f'Guard worker failed (optimized={optimized}): {process.stderr}')
            result = json.loads(process.stdout)
            ts.require(result['optimization_active'] == optimized, 'wrong interpreter optimization mode')
            for script, flag, value in cli_cases:
                process = subprocess.run(prefix + [str(code / script), flag, value],
                                         capture_output=True, text=True, timeout=30, check=False)
                ts.require(process.returncode == 2, f'CLI guard failed: {script} {flag} {value}')
                ts.require(bool(process.stderr.strip()), 'CLI failure lacks diagnostic')
            result['cli_rejection_checks'] = len(cli_cases)
            output_scripts = [('reproduce.py', ['--n', '1', '--k', '1']),
                              ('check_guards.py', ['--worker']),
                              ('numerics.py', ['--tail', '32', '--digits', '40']),
                              ('check_poles.py', [])]
            output_checks = []
            with tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                for script, extra_args in output_scripts:
                    for kind in ('regular_file', 'live_symlink', 'dangling_symlink'):
                        target = folder / (script + '-' + kind + '.json')
                        destination = folder / (script + '-' + kind + '-destination.json')
                        sentinel = b'pre-existing content must be preserved\n'
                        if kind == 'regular_file':
                            target.write_bytes(sentinel)
                        else:
                            if kind == 'live_symlink':
                                destination.write_bytes(sentinel)
                            target.symlink_to(destination)
                        # -S prevents importing site-installed dependencies, so
                        # these rejection checks cannot accidentally use SymPy.
                        process = subprocess.run(prefix + ['-S', str(code / script)] + extra_args
                                                 + ['--output', str(target)],
                                                 capture_output=True, text=True, timeout=30, check=False)
                        ts.require(process.returncode == 2,
                                   f'Output guard failed for {script}: {kind}')
                        ts.require('output error:' in process.stderr and 'already exists' in process.stderr,
                                   f'Output failure lacks clear diagnostic for {script}: {kind}')
                        ts.require(not process.stdout, 'Rejected output produced a misleading JSON result')
                        if kind == 'regular_file':
                            ts.require(target.read_bytes() == sentinel, 'Existing output content changed')
                        else:
                            ts.require(target.is_symlink() and target.readlink() == destination,
                                       'Output symlink changed')
                            if kind == 'live_symlink':
                                ts.require(destination.read_bytes() == sentinel, 'Symlink destination changed')
                            else:
                                ts.require(not destination.exists(), 'Dangling symlink destination was created')
                        output_checks.append({'script': script, 'target_kind': kind})
            failed_output_checks = 0
            with tempfile.TemporaryDirectory() as directory:
                for script, flag, value in [('reproduce.py', '--n', '257'),
                                            ('numerics.py', '--digits', '201')]:
                    target = Path(directory) / (script + '.json')
                    process = subprocess.run(prefix + [str(code / script), flag, value,
                                                       '--output', str(target)],
                                             capture_output=True, text=True, timeout=30, check=False)
                    ts.require(process.returncode == 2, 'Expected computation failure did not occur')
                    ts.require(not target.exists() and not target.is_symlink(),
                               'Failed computation left an output file')
                    failed_output_checks += 1
            result['failed_computation_output_checks'] = failed_output_checks
            result['output_rejection_checks'] = len(output_checks)
            result['output_rejection_cases'] = output_checks
            result['output_rejections_disable_site_packages'] = True
            result['mode'] = 'optimized' if optimized else 'normal'
            results.append(result)
        result = {'status': 'pass', 'modes': results}
    emit_json(parser, result, args.output)


if __name__ == '__main__':
    main()
