#!/usr/bin/env python3
"""Rebuild and independently audit the complete supplement, offline."""
from hashlib import sha256
from pathlib import Path
import gzip
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def run(relative, optimized=False):
    path = ROOT / relative
    args = [sys.executable] + (['-O'] if optimized else []) + [path.name]
    result = subprocess.run(args, cwd=path.parent, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError('Failed: ' + ' '.join(args) + '\n' +
                           result.stdout + result.stderr)
    parsed = json.loads(result.stdout)
    need(not isinstance(parsed, dict) or parsed.get('status', 'PASS') == 'PASS',
         'A checker returned a failure receipt')
    return {'script': relative, 'optimized_python': optimized,
            'exit_code': result.returncode}


def main():
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    for entry in provenance['imported_files']:
        data = (ROOT / entry['local']).read_bytes()
        need(sha256(data).hexdigest() == entry['sha256'],
             'Imported source changed: ' + entry['local'])

    circuits = {p.name: p.read_bytes() for p in (ROOT / 'circuits').glob('*.json')}
    need(len(circuits) == 4, 'Expected four literal circuit packets')
    binding = json.loads((ROOT / 'native' / 'COEFFICIENT_BINDING.json').read_text())
    coefficient_hashes = {entry['port']: entry['sha256']
                          for entry in binding['materialization']['files']}
    steps = [run('build.py')]
    for name, original in circuits.items():
        need((ROOT / 'circuits' / name).read_bytes() == original,
             'Circuit regeneration was not byte-identical: ' + name)

    steps.append(run('native/build_coefficients.py'))
    rebuilt = json.loads((ROOT / 'native' / 'COEFFICIENT_BINDING.json').read_text())
    need({entry['port']: entry['sha256'] for entry in rebuilt['materialization']['files']}
         == coefficient_hashes, 'Rebuilt complete tuple changed')
    for entry in rebuilt['materialization']['files']:
        raw = gzip.decompress((ROOT / 'native' / entry['file']).read_bytes())
        need(sha256(raw).hexdigest() == coefficient_hashes[entry['port']],
             'Rebuilt literal integer changed: ' + entry['port'])

    steps.append(run('native/audit_coefficients.py', optimized=True))
    steps.append(run('verify.py'))
    steps.append(run('verify.py', optimized=True))
    result = {'status': 'PASS', 'imported_source_files': len(provenance['imported_files']),
              'byte_identical_circuit_packets': len(circuits),
              'complete_tuple_raw_hashes_unchanged': True, 'steps': steps,
              'scope': 'Reproducible arithmetic and source audit; see PROOF.md for the ordinary semantic proof and its inherited dependencies.'}
    (ROOT / 'certificates' / 'REPRODUCE.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
