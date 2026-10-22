#!/usr/bin/env python3
"""Reproduce the finite arithmetic/compilation evidence, without a network.

Python 3.10+ standard library only. This verifies finite data and identities;
the universal equivalence is the mathematical proof in report.pdf.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_script(script, arguments, output):
    output.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, str(ROOT / script), *map(str, arguments)]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    require(result.returncode == 0,
            f'{script} failed:\n{result.stdout}\n{result.stderr}')
    return script


def compare(source, destination, names):
    for name in names:
        a, b = source / name, destination / name
        require(a.is_file() and b.is_file(), f'Missing generated/bundled {name}')
        require(a.read_bytes() == b.read_bytes(), f'Artifact differs: {b.relative_to(ROOT)}')
    return [str((destination / n).relative_to(ROOT)) for n in names]


def check_machine():
    raw = ROOT / 'coefficients/k215.tm'
    export = json.loads((ROOT / 'coefficients/k215_transitions.json').read_text())
    require(sha(raw) == export['source_sha256']['tm'], 'Literal machine hash differs')
    rows = []
    lines = raw.read_text().splitlines()
    require(lines[0] == '#! start 0', 'Wrong initial machine state')
    for line in lines[1:]:
        if not line.strip():
            continue
        state, read, write, direction, nxt = line.split()
        require(direction in ('L', 'R'), 'Unexpected move')
        rows.append([int(state), int(read), int(write), -1 if direction == 'L' else 1, int(nxt)])
    require(rows == export['transitions'], 'Literal/exported transition mismatch')
    require(len(rows) == 430, 'Transition count')
    require({tuple(r[:2]) for r in rows} == {(q, b) for q in range(215) for b in range(2)},
            'Missing or duplicate transition keys')
    require(all(r[2] in (0, 1) and 0 <= r[4] <= 215 for r in rows), 'Transition range')
    return dict(transitions=430, literal_sha256=sha(raw), status='passed')


def check_provenance():
    manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
    for entry in manifest['copied_sources']:
        data = (ROOT / entry['local_path']).read_bytes()
        require(hashlib.sha256(data).hexdigest() == entry['sha256'],
                f'Source SHA-256 mismatch: {entry["local_path"]}')
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        require(hashlib.sha1(blob).hexdigest() == entry['git_blob_sha1'],
                f'Source Git blob mismatch: {entry["local_path"]}')
    return dict(commit=manifest['commit'], files=len(manifest['copied_sources']), status='passed')


def check_manifest():
    manifest = ROOT / 'MANIFEST.sha256'
    if not manifest.is_file():
        return dict(status='not present during initial assembly')
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ', 1)
        target = ROOT / name
        require(target.is_file() and sha(target) == expected, f'Distribution hash mismatch: {name}')
        count += 1
    return dict(status='passed', files=count)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, default=ROOT / 'verification/REPRODUCTION.json')
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required')
    require(__debug__, 'Do not disable Python assertions for the bundled independent checks')
    provenance = check_provenance()
    machine = check_machine()
    distribution = check_manifest()
    compared = []
    with tempfile.TemporaryDirectory(prefix='con-zfc-reproduce-') as tmp:
        tmp = Path(tmp)
        jobs = [
            ('code/build_twelve.py', ['--degree', '--out', tmp / 'twelve'], tmp / 'twelve'),
            ('code/build_integer26.py', ['--degree', '--out', tmp / 'integer26'], tmp / 'integer26'),
            ('code/build_integer27.py', ['--out', tmp / 'integer27'], tmp / 'integer27'),
            ('coefficients/compiler5263.py', ['--output', tmp / 'coefficients'], tmp / 'coefficients'),
        ]
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = [pool.submit(run_script, *job) for job in jobs]
            for future in futures:
                print('Passed:', future.result(), flush=True)
        compared += compare(tmp / 'twelve', ROOT / 'data',
                            ['polynomial12.json', 'system12.json', 'residual_system12.json',
                             'sos12.json', 'verification12.json'])
        compared += compare(tmp / 'integer26', ROOT / 'data/integer26',
                            ['polynomial26.json', 'system26.json', 'residual_system26.json',
                             'sos26.json', 'verification26.json'])
        compared += compare(tmp / 'integer27', ROOT / 'data/integer27',
                            ['normalized27_poly114.json', 'normalized27_poly115.json',
                             'ordinary27_poly116.json', 'ordinary27_system107.json',
                             'ordinary27_sos124.json', 'verification.json'])
        compared += compare(tmp / 'coefficients', ROOT / 'coefficients',
                            ['windows5263.json', 'T5263_CONSTANTS.json', 'verification5263.json'])
        audit_path = tmp / 'independent26.json'
        run_script('code/audit_integer26.py',
                   ['--source', ROOT / 'data/integer26/polynomial26.json', '--out', audit_path], tmp)
        expected = ROOT / 'data/integer26_independent_checks.json'
        require(audit_path.read_bytes() == expected.read_bytes(), 'Independent norm audit differs')
        compared.append(str(expected.relative_to(ROOT)))
    receipt = dict(status='passed', source_provenance=provenance, machine_binding=machine,
                   distribution_manifest=distribution, regenerated_files=compared,
                   regenerated_file_count=len(compared), independent26_cases=27,
                   scope='Finite data, arithmetic, degree, and compiler checks. No fresh Lean/Rocq build; no K215 witness or consistency proof.')
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
