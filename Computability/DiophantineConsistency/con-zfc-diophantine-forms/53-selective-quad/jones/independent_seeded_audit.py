#!/usr/bin/env python3
"""Independent JSON-only provenance, live-ledger and actual-tuple degree audit.

No builder, primary checker, circuit module or upstream program is imported.
Degree propagation records the coefficient at the circuit's formal degree
bound on the diagonal x_i=t; a nonzero final coefficient proves attainment.
"""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def authenticate():
    pins = json.loads((ROOT / 'SOURCE_PINS.json').read_text())
    require(pins['commit'] == '124c07c0b77a9e20e84676514d8b1ff78536ea3f', 'source pin')
    for row in pins['files']:
        raw = (ROOT / row['local_path']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == row['sha256'], ('SHA256', row['local_path']))
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(blob == row['git_blob_sha'], ('Git blob', row['local_path']))
    binding = json.loads((ROOT / 'FIXED_BINDING.json').read_text())
    payloads = {}
    for row in binding['payloads']:
        packed = (ROOT / row['path']).read_bytes()
        raw = gzip.decompress(packed)
        require(hashlib.sha256(packed).hexdigest() == row['gzip_sha256'], 'gzip payload')
        require(hashlib.sha256(raw).hexdigest() == row['sha256'], 'raw payload')
        number = int.from_bytes(raw, 'little')
        require(number.bit_length() == row['bit_length'] and len(raw) == row['bytes'], 'payload length')
        payloads[row['name']] = number
    ports = [payloads[binding['port_aliases'][n]] for n in ['beta', 'K0', 'MC', 'MF']]
    return ports, binding, len(pins['files'])


def audit_circuit(body, ports, binding, prime):
    fixed = {name: pow(2, row['exponent'], prime)
             for name, row in binding['additional_fixed_leaves'].items()}
    for recipe in body['coefficient_recipes']:
        answer = 0
        for term in recipe['terms']:
            value = term['coefficient']
            for port, exponent in zip(ports, term['powers']):
                value = value * pow(port, exponent, prime) % prime
            answer = (answer + value) % prime
        fixed[recipe['name']] = answer
    operations = Counter()
    coefficients = []
    degree = []
    variables = []
    for index, node in enumerate(body['nodes']):
        kind = node['kind']
        if kind == 'variable':
            variables.append(node['name'])
            degree.append(1)
            coefficients.append(1)
        elif kind == 'literal':
            degree.append(0)
            coefficients.append(node['value'] % prime)
        elif kind == 'fixed':
            degree.append(0)
            coefficients.append(fixed[node['name']])
        else:
            require(kind in ['add', 'sub', 'mul'], ('node kind', kind))
            operations[kind] += 1
            left, right = node['left'], node['right']
            require(0 <= left < index and 0 <= right < index, 'topological ordering')
            if kind == 'mul':
                degree.append(degree[left] + degree[right])
                coefficients.append(coefficients[left] * coefficients[right] % prime)
            else:
                top = max(degree[left], degree[right])
                value = (coefficients[left] if degree[left] == top else 0)
                value += (1 if kind == 'add' else -1) * (coefficients[right] if degree[right] == top else 0)
                degree.append(top)
                coefficients.append(value % prime)
    require(len(variables) == 13 and set(variables) == set(body['variables']), '13 live variables')
    live = {body['output']}
    for index in range(len(body['nodes']) - 1, -1, -1):
        require(index in live, ('dead node', index))
        node = body['nodes'][index]
        if node['kind'] in ['add', 'sub', 'mul']:
            live.update([node['left'], node['right']])
    require(dict(operations) == body['operation_counts'], 'operation ledger')
    output = body['output']
    require(degree[output] == body['exact_degree'], 'reported degree')
    require(coefficients[output] != 0, 'diagonal degree coefficient vanished')
    return {'degree': degree[output], 'operations': sum(operations.values()),
            'operation_counts': dict(operations), 'prime': prime,
            'actual_tuple_diagonal_leader': coefficients[output]}


def main():
    ports, binding, sources = authenticate()
    result = {'status': 'PASS', 'pinned_source_files_verified': sources,
              'actual_payloads_verified': 4, 'variants': {},
              'scope': 'Exact finite provenance and circuit degree certificate, not compiler semantics.'}
    for name, count, deg in [('signed_seeded', 759, 57866184), ('signed', 770, 71382096)]:
        body = json.loads((ROOT / 'generated' / (name + '.json')).read_text())
        checks = [audit_circuit(body, ports, binding, p) for p in [101, 1009, 1000003]]
        require(all(c['operations'] == count and c['degree'] == deg for c in checks), 'expected metrics')
        result['variants'][name] = checks
    (ROOT / 'INDEPENDENT_AUDIT_RESULTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
