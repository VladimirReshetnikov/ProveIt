#!/usr/bin/env python3
"""Independent finite arithmetic audit of the final norm12 JSON packets.

Uses no imports from the candidate generator. The semantic proof is in
NORM12_INDEPENDENT_AUDIT.md. These checks are not a consistency test.
"""
import hashlib
import json
import random
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKETS = ROOT / 'arithmetic'
HERE = Path(__file__).resolve().parent


def evaluate(rows, values, prime=None):
    out = dict(values)
    for name, op, left, right in rows:
        a = left if isinstance(left, int) else out[left]
        b = right if isinstance(right, int) else out[right]
        value = a+b if op == '+' else a-b if op == '-' else a*b
        out[name] = value if prime is None else value % prime
    return out


def structure(packet):
    env = {name: 1 for name in packet['witnesses']}
    env.update({name: 0 for name in packet['fixed_numerals']})
    inputs = set(env)
    definitions = {}
    for row in packet['source']:
        name, op, a, b = row
        assert name not in env and op in ['+', '-', '*']
        da = 0 if isinstance(a, int) else env[a]
        db = 0 if isinstance(b, int) else env[b]
        env[name] = da+db if op == '*' else max(da, db)
        definitions[name] = (a, b)
    outputs = [packet['output']] if 'output' in packet else [x[0] for x in packet['comparisons']]
    required = set(outputs)
    stack = outputs[:]
    while stack:
        name = stack.pop()
        for arg in definitions.get(name, []):
            if isinstance(arg, str) and arg not in required:
                required.add(arg)
                stack.append(arg)
    assert inputs <= required
    assert set(definitions) <= required
    counts = Counter(row[1] for row in packet['source'])
    return {
        'unknowns': len(packet['witnesses']),
        'operations': len(packet['source']),
        'multiplications': counts['*'],
        'additions_subtractions': counts['+'] + counts['-'],
        'no_undefined_registers': True,
        'all_registers_and_ports_live': True,
        'degree_upper_bounds': {name: env[name] for name in outputs},
    }


def main():
    files = sorted(PACKETS.glob('norm12_*.json'))
    packets = {}
    results = []
    for path in files:
        packet = json.loads(path.read_text())
        if 'source' not in packet:
            continue
        packets[packet['name']] = packet
        result = structure(packet)
        assert result['operations'] == packet['ledger']['operations']
        result.update(file=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        results.append(result)

    system = packets['norm12_system']
    first_tail = next(i for i, row in enumerate(system['source']) if row[0] == 'H2')
    tail = system['source'][first_tail:]
    rng = random.Random(260012)
    exact_fixtures = 96
    for _ in range(exact_fixtures):
        root_u = rng.randrange(-9, 10)
        root_t = rng.randrange(-9, 10)
        data = {key: rng.randrange(-11, 12) for key in ['H','L','S','d','e','P','U']}
        data['G'] = root_u**2
        data['A'] = root_t**2
        got = evaluate(tail, data)
        want = 1
        for su in [-1, 1]:
            for st in [-1, 1]:
                gap = data['S']-data['L']*su*root_u-data['H']*data['L']*st*root_t
                fvalue = (data['d']*gap**2-data['H']**2*data['e'])**2
                fvalue -= 4*data['H']**4*data['P']*data['U']
                want *= fvalue
        assert got['N'] == want
        assert got['N1'] % 8 == 0
        assert (got['N']-got['N0']**2) % 64 == 0

    prime = 1009
    roots = {x*x % prime: x for x in range(prime)}
    accepted = 0
    attempts = 0
    while accepted < 128:
        attempts += 1
        values = {name: rng.randrange(-30, 31) for name in system['witnesses']+system['fixed_numerals']}
        got = evaluate(system['source'], values, prime)
        if got['G'] not in roots or got['A'] not in roots:
            continue
        ru, rt = roots[got['G']], roots[got['A']]
        B = 2*got['Q']*got['v']*got['b'] % prime
        expected = 1
        for su in [-1, 1]:
            for st in [-1, 1]:
                yH = got['S']-got['L']*su*ru-got['H']*got['L']*st*rt
                factor = (got['d']*yH*yH-got['H']**2*got['e'])**2
                factor -= got['H']**4 * B**2 * got['D']
                expected = expected*factor % prime
        assert got['N'] == expected
        product = evaluate(packets['norm12_product']['source'], values, prime)['polynomial']
        sos = evaluate(packets['norm12_sos']['source'], values, prime)['sos']
        assert product == (got['Nk']*got['Nt']*(1+got['N'])-1) % prime
        assert sos == ((got['Nk']-1)**2+(got['Nt']-1)**2+got['N']**2) % prime
        accepted += 1

    out = {
        'method': 'Independent JSON reader; exact four-conjugate scalar products at square radicands; finite-field four-root products for the full pipeline. No candidate generator imports.',
        'packets': results,
        'exact_integer_tail_fixtures': exact_fixtures,
        'full_circuit_finite_field_fixtures': accepted,
        'full_circuit_finite_field_attempts': attempts,
        'prime': prime,
        'mod64_guard_checked_in_every_exact_tail_fixture': True,
        'uniform_exact_degree_proof': 'NORM12_INDEPENDENT_AUDIT.md, Sections 9 and 10; all coefficients are certified uniformly for beta>0.',
        'scope': 'Finite implementation checks supplement the semantic proof. No halting K215 run, no consistency decision, and no new proof-assistant certificate.',
    }
    (HERE/'INDEPENDENT_CIRCUIT_AUDIT.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
