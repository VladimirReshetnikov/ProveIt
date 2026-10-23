#!/usr/bin/env python3
"""Independent packaging, ledger, payload and all-presentation degree diagnostics.

The circuits are parsed as inert JSON. No batching or upstream code is imported.
Finite rays prove degree attainment only; the unbounded upper-bound certificate
and solvability proof are the mathematical arguments in batching/PROOF.md.
"""
import gzip
import hashlib
import json
import random
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'batching'
PIN = '124c07c0b77a9e20e84676514d8b1ff78536ea3f'
EXPECTED = {
    'full_product': (117, 68, 49, [958]),
    'full_system': (113, 67, 46, [2, 956]),
    'full_shifted_system': (112, 67, 45, [2, 956]),
    'full_sos': (118, 69, 49, [1912]),
    'short_product': (115, 67, 48, [962]),
    'short_system': (111, 66, 45, [2, 960]),
    'short_shifted_system': (110, 66, 44, [2, 960]),
    'short_sos': (116, 68, 48, [1920]),
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def load_inputs():
    pins = json.loads((SOURCE / 'SOURCE_PINS.json').read_text())
    require(pins['commit'] == PIN, 'repository review pin')
    for row in pins['files']:
        data = (SOURCE / row['local_path']).read_bytes()
        require(sha256(data) == row['sha256'], ('source SHA256', row['local_path']))
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == row['git_blob_sha'], ('source Git blob', row['local_path']))
    binding = json.loads((SOURCE / 'COEFFICIENT_BINDING.json').read_text())
    old = (SOURCE / binding['source_binding_path']).read_bytes()
    require(sha256(old) == binding['source_binding_sha256'], 'original binding hash')
    adapter = (SOURCE / binding['source_adapter_proof_path']).read_bytes()
    require(sha256(adapter) == binding['source_adapter_sha256'], 'coefficient adapter hash')
    actual = {}
    for row in binding['payloads']:
        packed = (SOURCE / row['path']).read_bytes()
        raw = gzip.decompress(packed)
        value = int.from_bytes(raw, 'little')
        require(sha256(packed) == row['gzip_sha256'], ('gzip hash', row['name']))
        require(sha256(raw) == row['sha256'], ('raw hash', row['name']))
        require(len(raw) == row['bytes'], ('byte count', row['name']))
        require(value.bit_length() == row['bit_length'], ('bit length', row['name']))
        actual[row['name']] = value
    return {p: actual[n] for p, n in binding['port_aliases'].items()}, len(pins['files'])


def ledger(circuit, expected):
    inputs = circuit['witnesses'] + circuit['fixed_numerals']
    require(len(circuit['witnesses']) == 11, 'supplied variable count')
    available = set(inputs)
    counts = {'+': 0, '-': 0, '*': 0}
    for name, operation, x, y in circuit['source']:
        require(operation in counts, ('operation', operation))
        require(name not in available, ('duplicate register', name))
        require(all(isinstance(v, int) or v in available for v in (x, y)), ('register order', name))
        counts[operation] += 1
        available.add(name)
    outputs = [circuit['output']] if 'output' in circuit else [v for pair in circuit['comparisons'] for v in pair]
    live = {v for v in outputs if isinstance(v, str)}
    for name, operation, x, y in reversed(circuit['source']):
        require(name in live, ('dead gate', name))
        live.update(v for v in (x, y) if isinstance(v, str))
    require(set(inputs) <= live, 'dead supplied input')
    got = (sum(counts.values()), counts['*'], counts['+'] + counts['-'])
    require(got == expected[:3], ('ledger', circuit['name'], got, expected[:3]))
    require(circuit['ledger']['operations'] == got[0], 'reported ledger')
    return {'operations': got[0], 'multiplications': got[1], 'additions_subtractions': got[2]}


def polynomial_ray(circuit, ports, prime, seed):
    rng = random.Random(seed)
    env = {v: np.array([0, rng.randrange(1, prime)], dtype=np.int64)
           for v in circuit['witnesses']}
    env.update({v: np.array([ports[v] % prime], dtype=np.int64)
                for v in circuit['fixed_numerals']})

    def constant(value):
        return env[value] if isinstance(value, str) else np.array([value], dtype=np.int64)

    def trim(value):
        value = value % prime
        while len(value) > 1 and value[-1] == 0:
            value = value[:-1]
        return value

    def difference(x, y):
        answer = np.zeros(max(len(x), len(y)), dtype=np.int64)
        answer[:len(x)] += x
        answer[:len(y)] -= y
        return trim(answer)

    for name, operation, x, y in circuit['source']:
        x, y = constant(x), constant(y)
        if operation == '*':
            # At most 1139 terms of size <10038^2: safely below int64 overflow.
            require(max(len(x), len(y)) < 1200 and prime < 11000, 'convolution safety')
            answer = np.convolve(x, y)
        elif operation == '+':
            answer = np.zeros(max(len(x), len(y)), dtype=np.int64)
            answer[:len(x)] += x
            answer[:len(y)] += y
        else:
            answer = difference(x, y)
        env[name] = trim(answer)
    polynomials = ([constant(circuit['output'])] if 'output' in circuit else
                   [difference(constant(x), constant(y)) for x, y in circuit['comparisons']])
    return [{'degree': len(p) - 1, 'leading_coefficient': int(p[-1])} for p in polynomials]


def main():
    actual, sources = load_inputs()
    result = {'status': 'PASS', 'repository_pin': PIN,
              'pinned_source_files_verified': sources, 'payloads_verified': 4,
              'presentations': {}, 'polynomial_rays': 0,
              'scope': 'Independent finite diagnostics and provenance checks, not an end-to-end formal proof.'}
    for name, expected in EXPECTED.items():
        circuit = json.loads((SOURCE / (name + '.json')).read_text())
        entry = ledger(circuit, expected)
        entry['residual_degrees'] = expected[3]
        entry['rays'] = []
        for actual_ports in [False, True]:
            ports = actual if actual_ports else dict(zip(circuit['fixed_numerals'], [31, 127, 10, 45]))
            for prime, seed in [(10007, 901), (10009, 902), (10037, 903)]:
                rays = polynomial_ray(circuit, ports, prime, seed)
                require([r['degree'] for r in rays] == expected[3], ('degree', name, rays))
                result['polynomial_rays'] += len(rays)
                entry['rays'].append({'actual_ports': actual_ports, 'prime': prime, 'seed': seed, 'outputs': rays})
        result['presentations'][name] = entry
    (HERE / 'PACKAGE_AUDIT_RESULTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'presentations'}, indent=2))


if __name__ == '__main__':
    main()
