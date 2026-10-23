#!/usr/bin/env python3
"""Reconstruct and compare the complete inherited source-31 coefficient tuple.

The preserved upstream builder runs in a disposable staging directory with
its original expected directory layout. No repository checkout or network is
needed. The released builder and literal inputs are never modified.
"""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parent / 'upstream'
EXPECTED_BLOBS = {
    'build_coefficients.py': '27f0b25d7c0776d9d7bc042f6adb0c52285637bd',
    'k215_transitions.json': '4f6e42b6a22cb6d961ea814a05eb3a1394a40105',
    'wang943_tiles.json': 'a57902a6862352727fd925be406fa76371dd7edb',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git_blob(data):
    header = b'blob ' + str(len(data)).encode('ascii') + b'\0'
    return hashlib.sha1(header + data).hexdigest()


def verify_sources():
    provenance = json.loads((UPSTREAM / 'SOURCE_PROVENANCE.json').read_text())
    for source in provenance['sources']:
        data = (UPSTREAM / source['local_file']).read_bytes()
        require(len(data) == source['size_bytes'], 'Source length changed: ' + source['local_file'])
        require(git_blob(data) == source['git_blob_sha1'], 'Source Git blob changed: ' + source['local_file'])
        require(hashlib.sha256(data).hexdigest() == source['sha256'], 'Source SHA256 changed: ' + source['local_file'])
    for name, expected in EXPECTED_BLOBS.items():
        require(git_blob((UPSTREAM / name).read_bytes()) == expected, 'Required compiler input changed: ' + name)
    return len(provenance['sources'])


def main():
    source_count = verify_sources()
    with tempfile.TemporaryDirectory(prefix='proveit-native-reconstruction-') as temporary:
        stage = Path(temporary)
        (stage / 'upstream').mkdir()
        shutil.copyfile(UPSTREAM / 'build_coefficients.py', stage / 'build_coefficients.py')
        for name in ('k215_transitions.json', 'wang943_tiles.json'):
            shutil.copyfile(UPSTREAM / name, stage / 'upstream' / name)
        command = [sys.executable]
        if sys.flags.optimize:
            command.append('-O')
        command.append(str(stage / 'build_coefficients.py'))
        result = subprocess.run(command, cwd=stage, capture_output=True, text=True)
        require(result.returncode == 0,
                'Preserved builder failed:\n' + result.stdout + '\n' + result.stderr)
        binding = json.loads((stage / 'COEFFICIENT_BINDING.json').read_text())
        ports = []
        for name in ('beta', 'K', 'MC', 'MF_source'):
            rebuilt = gzip.decompress((stage / 'payloads' / (name + '.bin.gz')).read_bytes())
            delivered = gzip.decompress((HERE / 'payloads' / (name + '.bin.gz')).read_bytes())
            require(rebuilt == delivered, 'Reconstructed magnitude differs: ' + name)
            value = int.from_bytes(delivered, 'little')
            require(value > 0 and delivered == value.to_bytes((value.bit_length() + 7) // 8, 'little'),
                    'Noncanonical positive integer payload: ' + name)
            digest = hashlib.sha256(delivered).hexdigest()
            upstream_record = next(item for item in binding['files'] if item['port'] == name)
            require(digest == upstream_record['sha256'], 'Builder digest mismatch: ' + name)
            ports.append({'port': name, 'bit_length': value.bit_length(),
                          'raw_bytes': len(delivered), 'sha256': digest,
                          'matches_reconstructed_bytes': True})
        receipt = {
            'status': 'PASS',
            'source_snapshot': '124c07c0b77a9e20e84676514d8b1ff78536ea3f',
            'preserved_sources_verified': source_count,
            'builder_git_blob_sha1': EXPECTED_BLOBS['build_coefficients.py'],
            'builder_historical_source_commit': binding['source_commit'],
            'python_optimization_level': sys.flags.optimize,
            'instance': binding['instance'],
            'b': binding['b'], 'L': binding['L'], 'd': binding['d'],
            'ports': ports,
            'total_raw_bytes': sum(item['raw_bytes'] for item in ports),
            'native_basis_checks': binding['geometry']['native_basis_checks'],
            'tile_count': binding['geometry']['one_tile_clause_checks'],
            'geometry': binding['geometry'],
            'rank_controller': binding['padding'],
            'mask_checks': binding['mask_checks'],
            'scope': 'Exact finite reconstruction and byte equality; inherited unbounded compiler semantics remain a mathematical dependency.'
        }
    (HERE / 'REPRODUCTION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in (
        'status', 'preserved_sources_verified', 'python_optimization_level',
        'instance', 'b', 'L', 'd', 'ports', 'total_raw_bytes',
        'native_basis_checks', 'tile_count')}, indent=2))


if __name__ == '__main__':
    main()
