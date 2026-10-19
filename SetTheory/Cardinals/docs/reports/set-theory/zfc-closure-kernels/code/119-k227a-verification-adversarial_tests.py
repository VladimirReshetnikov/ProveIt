#!/usr/bin/env python3
"""Targeted rejection tests for the ordinary K227 verification drivers.

Python 3.10+ standard library only. This is a regression harness, not a proof
of checker soundness. It runs one valid symbolic case and deliberately invalid
inputs, never the complete universal runtime suite. All outputs go to a new
directory; existing receipts are never overwritten.

Example (paths may be changed for the packaged directory layout):
  python3 adversarial_tests.py --driver verify_runtime.py \
    --bootstrap-driver verify_bootstrap.py --engine-dir engine \
    --table k227_old.tm --sites sites_logical.json --output-dir adversarial_run
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

ENGINE_PINS = {
    'symbolic_runtime.py':
        'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
    'independent_runtime.py':
        '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
}
UNIVERSAL = 'UNIVERSAL_MATHEMATICAL_PASS'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def changed_target(raw, state, bit, target):
    lines, changed = [], 0
    for line in raw.splitlines():
        fields = line.split()
        if fields and not line.startswith('#') and tuple(map(int, fields[:2])) == (state, bit):
            fields[-1] = str(target)
            line = ' '.join(fields)
            changed += 1
        lines.append(line)
    require(changed == 1, 'Mutation did not identify exactly one transition')
    return '\n'.join(lines) + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('driver', 'bootstrap-driver', 'engine-dir', 'table', 'sites', 'output-dir'):
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--states', type=int, default=227)
    p.add_argument('--leaves', type=int, default=5121)
    p.add_argument('--cases', type=int, default=6656)
    a = p.parse_args()
    for name in ('driver', 'bootstrap_driver', 'engine_dir', 'table', 'sites', 'output_dir'):
        setattr(a, name, getattr(a, name).resolve())
    for name, expected in ENGINE_PINS.items():
        require(sha(a.engine_dir / name) == expected, 'Wrong pinned engine input: ' + name)
    require(not a.output_dir.exists(), 'Output directory must be new')
    a.output_dir.mkdir(parents=True)
    raw_table, original_sites = a.table.read_text(), json.loads(a.sites.read_text())
    require(original_sites and original_sites[0][1] != 'CH', 'Need a nonhalting first source instruction')
    receipt = {
        'format': 'k227-adversarial-checker-regressions-v1',
        'status': 'IN_PROGRESS',
        'scope': 'Targeted rejection tests and one valid prefix; no universal proof is inferred.',
        'harness_sha256': sha(__file__),
        'driver_sha256': sha(a.driver),
        'bootstrap_driver_sha256': sha(a.bootstrap_driver),
        'table_sha256': sha(a.table),
        'sites_sha256': sha(a.sites),
        'engine_pins': ENGINE_PINS,
        'expected_states': a.states,
        'expected_source_leaves': a.leaves,
        'expected_guarded_cases': a.cases,
        'python_version': sys.version,
        'tests': [],
    }
    report = a.output_dir / 'receipt.json'

    def save():
        report.write_text(json.dumps(receipt, indent=2) + '\n')

    def run_case(name, reason, *, table=None, sites=None, engine=None,
                 optimize=False, optimize_env=False, bootstrap_steps=None,
                 case_census=None, positive=False):
        directory = a.output_dir / name
        directory.mkdir()
        table_path, sites_path = a.table, a.sites
        if table is not None:
            table_path = directory / 'mutated.tm'
            table_path.write_text(table)
        if sites is not None:
            sites_path = directory / 'mutated_sites.json'
            sites_path.write_text(json.dumps(sites, indent=2) + '\n')
        output = directory / 'driver_receipt.json'
        command = [sys.executable] + (['-O'] if optimize else [])
        if bootstrap_steps is not None:
            command += [str(a.bootstrap_driver), '--table', str(table_path),
                        '--steps', str(bootstrap_steps), '--output', str(output)]
        else:
            command += [str(a.driver), '--engine-dir', str(engine or a.engine_dir),
                        '--table', str(table_path), '--sites', str(sites_path),
                        '--states', str(a.states), '--leaves', str(a.leaves),
                        '--cases', str(a.cases if case_census is None else case_census),
                        '--limit', '1', '--output', str(output)]
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        env['PYTHONDONTWRITEBYTECODE'] = '1'
        if optimize_env:
            env['PYTHONOPTIMIZE'] = '1'
        began = time.monotonic()
        result = subprocess.run(command, capture_output=True, text=True, env=env, timeout=45)
        (directory / 'stdout.txt').write_text(result.stdout)
        (directory / 'stderr.txt').write_text(result.stderr)
        proof = json.loads(output.read_text()) if output.exists() else {}
        if positive:
            ok = result.returncode == 0 and proof.get('status') == 'PARTIAL_PREFIX_PASS' and proof.get('cases') == 1
        else:
            ok = result.returncode != 0 and proof.get('status') != UNIVERSAL and reason in result.stderr
        record = {
            'name': name, 'result': 'EXPECTED_BEHAVIOR_PASS' if ok else 'UNEXPECTED_BEHAVIOR',
            'expected': 'Exactly one partial case, never universal PASS' if positive else 'Reject: ' + reason,
            'exit_code': result.returncode, 'driver_status': proof.get('status'),
            'driver_cases': proof.get('cases'), 'seconds': time.monotonic() - began,
            'table_sha256': sha(table_path), 'sites_sha256': sha(sites_path),
            'stderr_sha256': sha(directory / 'stderr.txt'),
            'stdout_sha256': sha(directory / 'stdout.txt'),
        }
        receipt['tests'].append(record)
        save()
        require(ok, 'Unexpected checker behavior: ' + name)

    def source_mutation(index, field, value):
        sites = [list(row) for row in original_sites]
        sites[index][field] = value
        return sites

    try:
        run_case('valid_prefix', '', positive=True)
        run_case('source_truncated', 'Incomplete binary tree', sites=original_sites[:-1])
        prefix = original_sites[0][0][:-1]
        require(prefix, 'Need a proper nonempty prefix for the mutation')
        run_case('source_prefix_collision', 'Leaf is also internal node',
                 sites=source_mutation(0, 0, prefix))
        run_case('source_unknown_opcode', 'Unknown instruction',
                 sites=source_mutation(0, 1, 'INVALID_OPCODE'))
        reg_index = next(i for i, row in enumerate(original_sites) if row[1] in ('CI', 'CD'))
        run_case('source_boolean_register', 'Bad register',
                 sites=source_mutation(reg_index, 2, True))
        run_case('source_wrong_census', 'Wrong source census', case_census=a.cases - 1)
        row = next(line for line in raw_table.splitlines() if line and not line.startswith('#'))
        run_case('table_missing_row', 'Missing row', table=raw_table.replace(row + '\n', '', 1))
        run_case('table_duplicate_row', 'Duplicate row', table=raw_table + row + '\n')
        states = [int(line.split()[0]) for line in raw_table.splitlines() if line and not line.startswith('#')]
        run_case('table_unknown_target', 'Bad targets',
                 table=changed_target(raw_table, 96, 0, max(states + [254]) + 1))
        first_bit = int(original_sites[0][0][0])
        run_case('runtime_premature_halt', 'KeyError: (254,',
                 table=changed_target(raw_table, 96, first_bit, 254))
        run_case('disabled_assertions_flag', 'Run with assertions enabled', optimize=True)
        run_case('disabled_assertions_environment', 'Run with assertions enabled', optimize_env=True)
        for index, name in enumerate(ENGINE_PINS):
            engine = a.output_dir / ('mutated_engine_' + str(index))
            engine.mkdir()
            for filename in ENGINE_PINS:
                shutil.copyfile(a.engine_dir / filename, engine / filename)
            with (engine / name).open('a') as stream:
                stream.write('\n# Harmless byte mutation: must fail the exact pin.\n')
            reason = 'Unexpected induction engine' if name == 'symbolic_runtime.py' else 'Unexpected runtime helper'
            run_case('pin_' + name.removesuffix('.py'), reason, engine=engine)
        halt_at_start = changed_target(raw_table, 95, 0, 254)
        run_case('bootstrap_premature_halt', 'Premature halt', table=halt_at_start, bootstrap_steps=2)
        run_case('bootstrap_wrong_frame', 'Wrong complete startup frame', bootstrap_steps=1)
        run_case('bootstrap_checks_survive_optimization', 'Premature halt',
                 table=halt_at_start, bootstrap_steps=2, optimize=True)
        require(sha(a.driver) == receipt['driver_sha256'] and
                sha(a.bootstrap_driver) == receipt['bootstrap_driver_sha256'] and
                sha(a.table) == receipt['table_sha256'] and sha(a.sites) == receipt['sites_sha256'],
                'An original input changed during the tests')
        receipt.update(status='ALL_TARGETED_REGRESSIONS_PASS',
                       total_tests=len(receipt['tests']),
                       accepted_prefix_tests=1, expected_rejections=len(receipt['tests']) - 1)
        save()
    except Exception as exc:
        receipt.update(status='REGRESSION_FAILURE', error=repr(exc))
        save()
        raise
    print(json.dumps({k: v for k, v in receipt.items() if k != 'tests'}, indent=2))


if __name__ == '__main__':
    main()
