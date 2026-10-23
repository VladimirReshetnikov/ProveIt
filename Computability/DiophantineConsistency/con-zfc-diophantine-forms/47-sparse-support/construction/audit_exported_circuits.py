#!/usr/bin/env python3
"""Independent, standard-library audit of the exported sparse circuits.

No release Python is imported or executed. This checks finite artifacts;
the semantic compiler theorem is a mathematical dependency, not a test.
"""
import argparse
import ast
from collections import Counter, defaultdict
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path


def require(p, msg):
    if not p:
        raise ValueError(msg)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def recipe_value(recipe, ports):
    if isinstance(recipe, dict):
        return 1 << recipe['power_of_two']
    return sum(t['coefficient'] * math.prod(x ** e for x, e in zip(ports, t['powers'])) for t in recipe)


def expression_value(source, ports):
    def visit(node):
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant):
            require(type(node.value) is int, 'noninteger expression leaf')
            return node.value
        if isinstance(node, ast.Name):
            return ports[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            return (-1 if isinstance(node.op, ast.USub) else 1) * visit(node.operand)
        require(isinstance(node, ast.BinOp), 'unsupported coefficient expression')
        a, b = visit(node.left), visit(node.right)
        if isinstance(node.op, ast.Add):
            return a + b
        if isinstance(node.op, ast.Sub):
            return a - b
        if isinstance(node.op, ast.Mult):
            return a * b
        require(isinstance(node.op, ast.Pow) and b >= 0, 'unsupported coefficient operation')
        return a ** b
    return visit(ast.parse(source, mode='eval'))


def read_fixed(root, name, ports):
    manifest = json.loads((root / name).read_text())
    out = {}
    for entry in manifest['live_fixed_coefficients']:
        packed = (root / entry['file']).read_bytes()
        raw = gzip.decompress(packed)
        require(digest(packed) == entry['gzip_sha256'], 'compressed leaf hash: ' + entry['name'])
        require(digest(raw) == entry['raw_sha256'], 'uncompressed leaf hash: ' + entry['name'])
        require(len(raw) >= 2 and raw[0] in (0, 1), 'signed leaf encoding')
        require(raw[-1] != 0 or len(raw) == 2, 'nonminimal magnitude')
        value = (-1 if raw[0] else 1) * int.from_bytes(raw[1:], 'little')
        require(value == recipe_value(entry['recipe'], ports), 'literal leaf recipe: ' + entry['name'])
        out[entry['name']] = value
    return out


def check_dag(path, fixed):
    raw = path.read_bytes()
    body = json.loads(raw)
    nodes = body['nodes']
    require(0 <= body['output'] < len(nodes), 'output index')
    counts = Counter()
    used_variables = set()
    used_fixed = set()
    for i, node in enumerate(nodes):
        kind = node['kind']
        require(kind in ('literal', 'variable', 'fixed', 'add', 'sub', 'mul'), 'nonpolynomial gate')
        if kind in ('add', 'sub', 'mul'):
            require(0 <= node['left'] < i and 0 <= node['right'] < i, 'nonacyclic gate')
            counts[kind] += 1
        elif kind == 'variable':
            used_variables.add(node['name'])
        elif kind == 'fixed':
            require(node['name'] in fixed, 'unbound coefficient')
            used_fixed.add(node['name'])
        else:
            require(type(node['value']) is int, 'noninteger literal')
    require(used_variables == set(body['variables']), 'variable declaration mismatch')
    require(dict(counts) == body['operation_counts'], 'operation ledger mismatch')
    live = set()
    todo = [body['output']]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        if nodes[i]['kind'] in ('add', 'sub', 'mul'):
            todo.extend((nodes[i]['left'], nodes[i]['right']))
    require(len(live) == len(nodes), 'unreachable declared gate')
    certificates = []
    for prime in (1000000007, 1000000009):
        degrees, leading = [], []
        for node in nodes:
            kind = node['kind']
            if kind == 'variable':
                degree, coefficient = 1, 1
            elif kind in ('fixed', 'literal'):
                degree = 0
                coefficient = (fixed[node['name']] if kind == 'fixed' else node['value']) % prime
            else:
                i, j = node['left'], node['right']
                if kind == 'mul':
                    degree, coefficient = degrees[i] + degrees[j], leading[i] * leading[j] % prime
                else:
                    degree = max(degrees[i], degrees[j])
                    left = leading[i] if degrees[i] == degree else 0
                    right = leading[j] if degrees[j] == degree else 0
                    coefficient = (left + right if kind == 'add' else left - right) % prime
            degrees.append(degree)
            leading.append(coefficient)
        output = body['output']
        certificates.append({'modulus': prime, 'degree_upper_bound': degrees[output], 'coefficient_at_bound': leading[output]})
    return body, {'file': path.name, 'sha256': digest(raw), 'operations': sum(counts.values()), 'counts': dict(counts), 'variables': len(used_variables), 'fixed_leaves': len(used_fixed), 'degree_certificates': certificates}


def sparse_audit(body):
    weights = [0] + body['weights']
    W = max(weights)
    require(len(weights) == 32 and len(set(weights)) == 32 and min(weights) == 0, 'weight shape')
    require(body['target_offset'] == -1, 'release source must use the minimal target offset')
    require([row['target_exponent'] for row in body['rows']] == [(j + 1) * (2 * W + 1) - 1 for j in range(22)], 'release target positions')
    pairs = defaultdict(list)
    for i in range(32):
        for j in range(i, 32):
            pairs[weights[i] + weights[j]].append((i, j))
    support = {tuple(t['alpha']) for row in body['rows'] for t in row['terms']}
    for alpha in support:
        pair = [i + 1 for i, e in enumerate(alpha) for _ in range(e)]
        pair = tuple([0] * (2 - len(pair)) + pair)
        require(len(pair) == 2, 'not quadratic')
        require(pairs[weights[pair[0]] + weights[pair[1]]] == [pair], 'supported pair collision')
    checks = 0
    for shift in (0, -1):  # Jones nine-natural and Sun ten-integer source conventions.
        targets = [(j + 1) * (2 * W + 1) + shift for j in range(22)]
        for h, row in zip(targets, body['rows']):
            for term in row['terms']:
                alpha = term['alpha']
                e = sum(a * w for a, w in zip(alpha, weights[1:]))
                require(h >= e, 'negative encoded exponent')
                for s, preimages in pairs.items():
                    checks += len(preimages)
                    if h - e + s in targets:
                        require(h - e + s == h and s == e and len(preimages) == 1, 'cross-target contamination')
    return {'maximum_weight': W, 'support': len(support), 'all_degree_at_most_two_monomials': 528, 'distinct_pair_sums': len(pairs), 'record_pair_checks_across_both_conventions': checks}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('release', type=Path)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    root = args.release
    native = json.loads((root / 'fixed_coefficients.json').read_text())
    require(native['source_pin'] == '124c07c0b77a9e20e84676514d8b1ff78536ea3f', 'snapshot pin')
    ports = []
    port_report = []
    for entry in native['four_ports']:
        packed = (root / entry['file']).read_bytes()
        raw = gzip.decompress(packed)
        require(digest(packed) == entry['gzip_sha256'] and digest(raw) == entry['raw_sha256'], 'native port hash')
        value = int.from_bytes(raw, 'little')
        require(value.bit_length() == entry['bit_length'], 'native port bit length')
        ports.append(value)
        port_report.append({'name': entry['name'], 'raw_sha256': digest(raw), 'bit_length': value.bit_length()})
    fixed9 = read_fixed(root, 'fixed_coefficients.json', ports)
    fixed10 = read_fixed(root, 'fixed_coefficients10.json', ports)
    require(digest((root / 'parent_system.json').read_bytes()) == 'ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48', 'parent binding')
    source_reports, circuit_reports = [], []
    for W in (220, 239):
        source = json.loads((root / f'targets_sparse{W}.json').read_text())
        source_reports.append(sparse_audit(source))
        pv = dict(zip(source['ports'], ports))
        coefficients = [expression_value(t['weighted_coefficient'], pv) for row in source['rows'] for t in row['terms']]
        require(max(abs(x) for x in coefficients) < (1 << 2134927), 'nine source coefficient bound')
        for kind in ('positive', 'natural', 'positive_degree_certificate', 'natural_degree_certificate'):
            body, report = check_dag(root / 'generated' / f'sparse{W}_nine_{kind}.json', fixed9)
            require(body['W'] == W and body['weights'] == source['weights'], 'nine source weights')
            require(body['target_records_sha256'] == digest((root / f'targets_sparse{W}.json').read_bytes()), 'nine target binding')
            if 'certificate' in kind:
                for cert in report['degree_certificates']:
                    p = cert['modulus']
                    expected = pow(2, 2050, p) * pow(pow(2, 2134939, p), 54148 * W + 26496, p) % p
                    require(cert['degree_upper_bound'] == 108296 * W + 53272 and cert['coefficient_at_bound'] == expected != 0, 'nine exact degree')
                report['degree_status'] = 'exact; requires the proved algebraic identity with the advertised evaluator'
            else:
                report['degree_status'] = 'cancellation occurs; exact degree is certified by the algebraically equal certificate form'
            circuit_reports.append(report)
        body, report = check_dag(root / 'generated' / f'sparse{W}_ten_integer.json', fixed10)
        require(body['source_parameters']['maximum_weight'] == W, 'ten weight maximum')
        rows = body['coefficient_recipes']['rows']
        for original, transformed in zip(source['rows'], rows):
            src = {tuple(t['alpha']): expression_value(t['weighted_coefficient'], pv) for t in original['terms']}
            dst = {tuple(t['alpha']): t['sign'] * (t['leaf'] if isinstance(t['leaf'], int) else fixed10[t['leaf']]) for t in transformed}
            require(src == dst, 'ten coefficient-row binding')
        for cert in report['degree_certificates']:
            require(cert['degree_upper_bound'] == 297088 * W + 147144 and cert['coefficient_at_bound'] != 0, 'ten exact degree')
        report['degree_status'] = 'exact from a nonzero diagonal coefficient at the propagated upper bound'
        circuit_reports.append(report)
    result = {'status': 'PASS', 'scope': 'Independent finite data, coefficient binding, sparse extraction, DAG, and exact-degree checks; does not decide consistency or supply an end-to-end formal proof', 'native_ports': port_report, 'source_variants': source_reports, 'circuits': circuit_reports}
    text = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(text)
    print(json.dumps({'status': result['status'], 'source_variants': source_reports, 'circuits': [{'file': r['file'], 'operations': r['operations'], 'degree': r['degree_certificates'][0]['degree_upper_bound'], 'residue': r['degree_certificates'][0]['coefficient_at_bound']} for r in circuit_reports]}, indent=2))


if __name__ == '__main__':
    main()
