#!/usr/bin/env python3
"""Small shared, standard-library-only circuit validation helpers."""
from collections import Counter
from hashlib import sha256
import json

PORTS = ['beta', 'K0', 'MC', 'MF']
ALIASES = {'Bm1': 'beta', 'Kconstant': 'K0'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return sha256(data).hexdigest()


def source_digest(source):
    return digest(json.dumps(source, separators=(',', ':')).encode())


def normalized_ports(packet):
    p = dict(packet)
    p['fixed_numerals'] = [ALIASES.get(x, x) for x in p['fixed_numerals']]
    p['source'] = [[ALIASES.get(n, n), op,
                    ALIASES.get(a, a) if isinstance(a, str) else a,
                    ALIASES.get(b, b) if isinstance(b, str) else b]
                   for n, op, a, b in p['source']]
    return p


def audit_dag(packet, check_ledger=True):
    witnesses = packet['witnesses']
    ports = packet['fixed_numerals']
    require(len(witnesses) == len(set(witnesses)), 'duplicate witness')
    require(len(ports) == len(set(ports)), 'duplicate fixed port')
    require(not set(witnesses) & set(ports), 'witness is also a fixed coefficient')
    degree = {n: 1 for n in witnesses}
    degree.update({n: 0 for n in ports})
    for row in packet['source']:
        require(isinstance(row, list) and len(row) == 4, 'invalid gate row')
        n, op, a, b = row
        require(isinstance(n, str) and n not in degree, 'duplicate or invalid gate name')
        require(op in ('+', '-', '*'), 'non-polynomial operation')
        require(all(type(x) is int or (isinstance(x, str) and x in degree)
                    for x in (a, b)), 'undefined operand at ' + n)
        da = 0 if type(a) is int else degree[a]
        db = 0 if type(b) is int else degree[b]
        degree[n] = da + db if op == '*' else max(da, db)
    require(('output' in packet) != ('comparisons' in packet),
            'circuit must have exactly one output kind')
    if 'output' in packet:
        outputs = [packet['output']]
    else:
        require(bool(packet['comparisons']), 'system has no equations')
        require(all(isinstance(row, list) and len(row) == 2
                    for row in packet['comparisons']), 'bad comparison')
        outputs = [x for row in packet['comparisons'] for x in row]
    require(all(type(x) is int or (isinstance(x, str) and x in degree)
                for x in outputs), 'undefined output')
    live = {x for x in outputs if isinstance(x, str)}
    for n, op, a, b in reversed(packet['source']):
        require(n in live, 'dead gate ' + n)
        live.update(x for x in (a, b) if isinstance(x, str))
    require(set(witnesses + ports) <= live, 'unused witness or coefficient port')
    counts = Counter(row[1] for row in packet['source'])
    ledger = dict(operations=len(packet['source']), multiplications=counts['*'],
                  additions_subtractions=counts['+'] + counts['-'],
                  all_gates_live=True, all_ports_live=True)
    if check_ledger:
        supplied = packet.get('ledger', {})
        require(supplied.get('operations') == ledger['operations'], 'operation ledger mismatch')
        require(supplied.get('multiplications', supplied.get('M')) == ledger['multiplications'],
                'multiplication ledger mismatch')
        require(supplied.get('additions_subtractions', supplied.get('A')) == ledger['additions_subtractions'],
                'addition ledger mismatch')
    ledger['syntactic_degree_upper_bounds'] = {
        x: degree[x] for x in outputs if isinstance(x, str)}
    return ledger


def evaluate(packet, values, modulus):
    v = dict(values)
    for n, op, a, b in packet['source']:
        a = a if type(a) is int else v[a]
        b = b if type(b) is int else v[b]
        v[n] = (a + b if op == '+' else a - b if op == '-' else a * b) % modulus
    return v


def residual_values(packet, values, modulus):
    v = evaluate(packet, values, modulus)
    def get(x):
        return x if type(x) is int else v[x]
    if 'output' in packet:
        return [get(packet['output']) % modulus]
    return [(get(a) - get(b)) % modulus for a, b in packet['comparisons']]
