#!/usr/bin/env python3
"""Offline exact checks of the complete release; never mutates its inputs."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
COMPONENTS = ('integer286', 'natural235', 'positive10', 'integer11')


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    manifest = read(ROOT / 'MANIFEST_SHA256.json')
    for relative, pin in manifest['files'].items():
        path = ROOT / relative
        need(path.is_file(), 'Missing release file: ' + relative)
        need(path.stat().st_size == pin['bytes'], 'Wrong file size: ' + relative)
        need(digest(path) == pin['sha256'], 'Release hash mismatch: ' + relative)
    return len(manifest['files'])


def check_catalog():
    catalog = read(ROOT / 'ENDPOINTS.json')
    need(len(catalog['endpoints']) == 9, 'Nine endpoints required')
    summaries = []
    for item in catalog['endpoints']:
        path = ROOT / item['equation_path']
        need(digest(path) == item['equation_sha256'], 'Equation hash: ' + item['id'])
        equation = read(path)
        need(equation['domain'] == item['domain'], 'Domain: ' + item['id'])
        if item['representation'] == 'sum_of_quadratic_squares':
            poly_path = ROOT / item['expanded_polynomial_path']
            need(digest(poly_path) == item['expanded_polynomial_sha256'], 'Expansion hash')
            poly = read(poly_path)
            metrics = dict(variables=len(equation['variables']),
                           rows=len(equation['residuals']),
                           degree=max(len(m) for c, m in poly['terms']),
                           monomials=len(poly['terms']),
                           height=max(abs(c) for c, m in poly['terms']))
        else:
            variables = equation.get('variables', equation.get('witnesses'))
            metrics = dict(variables=len(variables), degree=equation['exact_degree'],
                           operations=equation['operations'])
        need(metrics == item['metrics'], 'Endpoint catalog metrics: ' + item['id'])
        summaries.append(dict(id=item['id'], domain=item['domain'], **metrics))
    return summaries


def invoke(command, cwd):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True, env=env)
    need(result.returncode == 0,
         'Command failed: ' + ' '.join(command) + '\n' + result.stdout + result.stderr)
    return result.stdout


def component_run(name, rebuild, temporary_root):
    folder = temporary_root / name
    shutil.copytree(ROOT / name, folder)
    modes = {}
    for optimized in (False, True):
        mode = 'optimized' if optimized else 'normal'
        python = [sys.executable] + (['-O'] if optimized else []) + ['-B']
        rebuilt_files = []
        if rebuild and name == 'integer11':
            names = ('parity_saturated11_native.json', 'parity_saturated11_short.json',
                     'METRICS.json')
            before = {relative: (folder / relative).read_bytes() for relative in names}
            invoke(python + ['build.py'], folder)
            for relative, expected in before.items():
                need((folder / relative).read_bytes() == expected,
                     'Signed-circuit byte rebuild: ' + relative)
                rebuilt_files.append(relative)
        command = python + ['verify.py']
        if rebuild and name in ('integer286', 'natural235'):
            command.append('--rebuild')
        receipt = json.loads(invoke(command, folder))
        if name == 'integer11':
            receipt = read(folder / ('CHECK_OPTIMIZED.json' if optimized else 'CHECK.json'))
            receipt['byte_exact_rebuilt_files'] = rebuilt_files
        if name != 'natural235':
            need(receipt.get('status') == 'PASS', 'Missing PASS: ' + name)
        modes[mode] = receipt
    return modes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true',
                        help='Replay all component producers in isolated directories')
    parser.add_argument('--receipt', type=Path,
                        help='Write a detailed receipt at the requested path')
    args = parser.parse_args()
    need(sys.version_info >= (3, 10), 'Python 3.10 or newer is required')
    count = check_manifest()
    endpoints = check_catalog()
    appendix = invoke([sys.executable, '-B', str(ROOT / 'report/generate_tables.py'),
                       '--check'], ROOT).strip()
    components = {}
    with tempfile.TemporaryDirectory(prefix='conzfc-complete-replay-') as temporary:
        with ThreadPoolExecutor(max_workers=4) as pool:
            jobs = {pool.submit(component_run, name, args.rebuild, Path(temporary)): name
                    for name in COMPONENTS}
            for job in as_completed(jobs):
                name = jobs[job]
                components[name] = job.result()
                print('PASS: ' + name + ' (normal and optimized)', file=sys.stderr)
    result = dict(status='PASS', manifest_files=count, deterministic_rebuilds=args.rebuild,
                  modes=['normal', 'optimized'], manuscript=appendix, endpoints=endpoints,
                  components={name: components[name] for name in COMPONENTS},
                  proof_boundary='Finite exact artifacts, algebra, and transformations; '
                  'unbounded arithmetic and logical calibration are ordinary proofs, '
                  'not established by these tests. No new end-to-end proof-assistant build.')
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(status='PASS', manifest_files=count,
                         endpoints=len(endpoints), component_runs=8,
                         deterministic_rebuilds=args.rebuild, manuscript=appendix), indent=2))


if __name__ == '__main__':
    main()
