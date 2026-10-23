#!/usr/bin/env python3
"""Finite arithmetic diagnostics for the new eleven-variable construction.

These checks do not replace ELEVEN_POSITIVE_PROOF.md or the inherited
compiler and K215 logical calibration. No third-party dependency is needed.
"""
import argparse
import gzip
import hashlib
import json
import math
import random
from fractions import Fraction
from pathlib import Path
from build_eleven import build, evaluate, audit_live, WITNESSES, PORTS

HERE = Path(__file__).resolve().parent

def need(test, message):
    if not test: raise AssertionError(message)

def conjugate_norm(values, modulus=None, old_carrier=False):
    """Independent multiplication in the rank-eight formal quadratic algebra."""
    G, A, D = values['G'], values['A'], values['D']
    def reduce(value): return value if modulus is None else value % modulus
    def mul(x, y):
        out = [0] * 8
        for i, a in enumerate(x):
            for j, b in enumerate(y):
                multiplier = ((G if i & j & 1 else 1) *
                              (A if i & j & 2 else 1) *
                              (D if i & j & 4 else 1))
                out[i ^ j] += multiplier * a * b
        return [reduce(a) for a in out]
    if old_carrier:
        E = values['E']
        inverse = Fraction(1, E) if modulus is None else pow(E, -1, modulus)
        corrected_t = values['t'] + (values['k'] - values['R'] - 1) * inverse
        S = values['H']
        L = values['L0']
        W = L * values['b0'] + S * corrected_t
    else:
        S, L, W = values['S'], values['L'], values['W']
    ee = values['Q'] * (D * values['v'] ** 2 + values['b'] ** 2) - 1
    bb = 2 * values['Q'] * values['v'] * values['b']
    out = [1] + [0] * 7
    for sg in (-1, 1):
        for sa in (-1, 1):
            for sf in (-1, 1):
                argument = [W, -sg * L, -sa * S * values['M'], 0, 0, 0, 0, 0]
                factor = [values['d'] * a for a in mul(argument, argument)]
                factor[0] -= S * S * ee
                factor[4] += sf * S * S * bb
                out = mul(out, [reduce(a) for a in factor])
    need(not any(out[1:]), 'formal conjugates did not descend to a scalar')
    return out[0]

def univariate(packet, coefficients, prime):
    """Full coefficient arrays over F_p[lambda], not degree propagation."""
    def trim(a):
        while len(a) > 1 and not a[-1]: a.pop()
        return a
    def add(a, b, sign):
        out = [0] * max(len(a), len(b))
        for j, x in enumerate(a): out[j] = x
        for j, x in enumerate(b): out[j] = (out[j] + sign * x) % prime
        return trim(out)
    def mul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for j, x in enumerate(a):
            if x:
                for k, y in enumerate(b):
                    out[j + k] = (out[j + k] + x * y) % prime
        return trim(out)
    values = {name: [0, coefficients[name] % prime] for name in WITNESSES}
    values.update({name: [coefficients[name] % prime] for name in PORTS})
    for name, operation, left, right in packet['source']:
        left = [left % prime] if isinstance(left, int) else values[left]
        right = [right % prime] if isinstance(right, int) else values[right]
        values[name] = mul(left, right) if operation == '*' else add(left, right, 1 if operation == '+' else -1)
    return {name: (len(value) - 1, value[-1]) for name, value in values.items()}

def check_leading(prime, seed):
    rng = random.Random(seed)
    coefficients = {name: rng.randrange(1, 20) for name in WITNESSES}
    coefficients.update(dict(zip(PORTS, (31, 127, 10, 45))))
    results = univariate(build(), coefficients, prime)
    q0 = coefficients['beta'] * coefficients['J']
    k0 = coefficients['eta'] + coefficients['zeta']
    s0 = coefficients['s'] + 3 * q0
    nlead = (2 ** 46 * coefficients['i'] ** 48 * k0 ** 96 * coefficients['w'] ** 90 *
             s0 ** 192 * q0 ** 710 * (q0 - coefficients['F']) ** 16) % prime
    transport_lead = (coefficients['w'] * (q0 - coefficients['F'] - coefficients['alpha']) -
                      coefficients['z'] * q0)
    plead = nlead * transport_lead % prime
    need(nlead and plead, 'degenerate ray chosen')
    need(results['N'] == (1152, nlead), 'norm degree or highest coefficient mismatch: ' + repr(results['N']))
    need(results['polynomial'] == (1154, plead), 'product degree or highest coefficient mismatch')
    return {'prime': prime, 'seed': seed, 'norm': list(results['N']), 'product': list(results['polynomial'])}

def parameter_bound_checks():
    rng = random.Random(11031154)
    total = 0
    failed_old_bootstrap = 0
    for q in (16, 17, 32, 257):
        for _ in range(80):
            w = rng.randrange(1, 1000000)
            s = rng.randrange(1, 100)
            eta = rng.randrange(1, 5)
            zeta = rng.randrange(1, 5)
            i = rng.randrange(1, 100)
            T = rng.randrange(1, 1000000)
            R = rng.randrange(3*q+1, q**4-2)
            X = w*q
            s0 = s+3*q
            Y = s0*q**3
            E = X*Y
            k = eta+zeta
            c = k*Y+eta
            a = E+Y
            H = 4*a+3
            Delta = a*a+H
            ell = E*k*Y
            I = i*c*c
            D = 1+Delta*I*I
            Q = Delta*Delta*I*I
            b = c+R*D
            Cstar = E+2*(X+Y)+s0*q*q
            M = I*(2*T+R*Cstar*i*c)
            # A strict integer majorant for every |y|, from the proved estimate.
            y_bound = c*T*((a+2)*I+1)+c+R*D+1
            need(b <= Q-1, 'b<=d failed')
            need(y_bound < M*ell, 'sharp weight insufficient without k>E')
            need(E//math.gcd(E,H) > R, 'short-index modulus bound failed')
            need(E+k-R-1 > 0, 'carrier positivity failed')
            total += 1
            failed_old_bootstrap += k <= E
    return {'parameter_cases': total, 'cases_with_k_le_E': failed_old_bootstrap,
            'sharp_integer_majorant': 'verified on all cases', 'modulus_lower_bound': 'verified on all cases'}

def check_binding(compiler):
    binding_path = compiler/'COEFFICIENT_BINDING.json'
    binding_raw = binding_path.read_bytes()
    binding = json.loads(binding_raw)
    ports = {}
    hashes = {}
    alias = {'beta': 'beta', 'K': 'K0', 'MC': 'MC', 'MF_source': 'MF'}
    for record in binding['materialization']['files']:
        compressed = (compiler/record['file']).read_bytes()
        raw = gzip.decompress(compressed)
        digest = hashlib.sha256(raw).hexdigest()
        need(digest == record['sha256'], 'coefficient payload digest mismatch')
        need(hashlib.sha256(compressed).hexdigest() == record['gzip_sha256'], 'coefficient gzip digest mismatch')
        value = int.from_bytes(raw, 'little')
        need(value.bit_length() == record['bits'], 'coefficient bitlength mismatch')
        ports[alias[record['port']]] = value
        hashes[alias[record['port']]] = digest
    need(set(ports) == set(PORTS), 'whole four-port tuple not supplied')
    need(ports['beta'] == (1 << binding['d'])-1, 'wrong fixed base')
    rng = random.Random(678139)
    count = 0
    for prime in (1000000007, 1000000009):
        residues = {name: value % prime for name, value in ports.items()}
        for _ in range(20):
            assignment = {name: rng.randrange(-5, 6) for name in WITNESSES}
            assignment.update(residues)
            values = evaluate(build(), assignment, prime)
            need(values['N'] == conjugate_norm(values, prime), 'norm mismatch at actual fixed coefficient residues')
            count += 1
    return {'instance': binding['instance'], 'binding_sha256': hashlib.sha256(binding_raw).hexdigest(),
            'port_payload_sha256': hashes, 'modular_norm_cases_at_actual_tuple': count,
            'scope': 'Exact byte/port binding plus algebra checks; compiler semantic theorem is separate.'}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler', type=Path, default=HERE.parent/'compiler')
    args = parser.parse_args()
    rng = random.Random(2026102311)
    packet = build()
    for kind in ('product', 'system', 'shifted_system'): audit_live(build(kind))
    primes = (1000000007, 1000000009, 1000033)
    algebra_cases = 0
    carrier_cases = 0
    for prime in primes:
        for _ in range(30):
            assignment = {name: rng.randrange(-7, 8) for name in WITNESSES+PORTS}
            values = evaluate(packet, assignment, prime)
            need(values['N'] == conjugate_norm(values, prime), 'scalar norm identity failed')
            if values['E']:
                old = conjugate_norm(values, prime, old_carrier=True)
                need(values['N'] == pow(values['E'], 16, prime) * old % prime, 'denominator absorption identity failed')
                carrier_cases += 1
            shifted = evaluate(build('shifted_system'), assignment, prime)
            old_values = evaluate(packet, dict(assignment, z=assignment['z']+1), prime)
            need((old_values['Nt']-1) % prime ==
                 (shifted['transport_left']-shifted['transport_right']) % prime,
                 'transport shift identity failed')
            algebra_cases += 1
    parity_cases = 0
    for _ in range(500):
        assignment = {name: rng.randrange(-100, 101) for name in WITNESSES+PORTS}
        values = evaluate(packet, assignment, 4)
        need(values['N'] in (0, 1), 'mod4 unit guard failed')
        parity_cases += 1
    exact_cases = 0
    for _ in range(5):
        assignment = {name: rng.randrange(-2, 4) for name in WITNESSES+PORTS}
        values = evaluate(packet, assignment)
        need(values['N'] == conjugate_norm(values), 'exact integer norm identity failed')
        if values['E']:
            need(values['N'] == values['E']**16*conjugate_norm(values, old_carrier=True),
                 'exact rational carrier identity failed')
        exact_cases += 1
    result = {
        'algebra_cases_over_prime_fields': algebra_cases,
        'denominator_absorption_cases': carrier_cases,
        'exact_integer_and_rational_cases': exact_cases,
        'mod4_guard_cases': parity_cases,
        'all_gates_and_inputs_live': True,
        'full_polynomial_degrees': [check_leading(1000000007, 43), check_leading(1000000009, 47)],
        'parameter_bounds': parameter_bound_checks(),
        'ledgers': {kind: build(kind)['ledger'] for kind in ('product', 'system', 'shifted_system')},
        'fixed_tuple_binding': check_binding(args.compiler),
        'scope': 'Finite algebraic diagnostics and measured gates; unbounded proof and inherited compiler dependencies are separate.'}
    (HERE/'generated'/'CHECK_RESULTS.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
