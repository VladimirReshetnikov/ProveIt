#!/usr/bin/env python3
"""Read-only compiler audit for the standalone linear witness-height companion.

Imports the original emitter without editing it. Output is written only to the
explicitly requested external output path. The proof, not this finite corpus, establishes
the all-source and all-input claims. Generic Circuit.integer is NOT assumed linear.
"""
import argparse
import gc
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

PACKET_REFERENCE = 'parallel-diophantine-certificate-research-20261003'
PINNED_FILES = ('PROOF.md', 'compiler.py', 'circuit.py', 'frozen_lazy_source.py', 'frozen_reversible_binary.py', 'fixtures.json')

def check(condition, *message):
    if not condition:
        raise RuntimeError(message)

def file_hashes(packet):
    return {name: hashlib.sha256((packet / name).read_bytes()).hexdigest() for name in PINNED_FILES}

def bound_polynomial(poly, tags, weights):
    """Return (coordinate-dependence tag in {0,1}, coefficient L1 majorant).

A natural variable i obeys v_i <= weights[i]*(R+1)**tags[i].
A polynomial is admissible only if every monomial has tag sum <=1.
"""
    tag, weight = 0, 0
    for monomial, coefficient in poly.items():
        degree = sum(tags[i] for i in monomial)
        check(degree <= 1, 'nonlinear height monomial', monomial, degree)
        term = abs(coefficient)
        for i in monomial:
            term *= weights[i]
        weight += term
        tag = max(tag, degree)
    return tag, weight

def audit_operations(circuit):
    tags = [1] * circuit.input_count
    weights = [1] * circuit.input_count
    counts = {'integer': 0, 'ge': 0, 'boolean': 0}
    max_monomial_height_degree = 0
    for op, poly in circuit.ops:
        tag, weight = bound_polynomial(poly, tags, weights)
        max_monomial_height_degree = max(max_monomial_height_degree, tag)
        counts[op] += 1
        if op == 'integer':
            tags.extend((tag, tag))
            weights.extend((weight, weight))
        elif op == 'ge':
            tags.extend((0, tag))
            weights.extend((1, weight))
        else:
            check(op == 'boolean', 'unknown operation', op)
            # PROOF.md's gate-use audit proves these are Boolean-valued. This
            # further structural assertion rules out coordinate-dependent inputs.
            check(tag == 0, 'coordinate-valued input to Boolean arithmetic', poly)
            tags.append(0)
            weights.append(1)
    check(len(weights) == len(circuit.names), 'operation allocation mismatch')
    return tags, weights, {
        'operation_counts': counts,
        'witness_count': len(weights) - circuit.input_count,
        'H': max(weights[circuit.input_count:], default=1),
        'maximum_height_degree': max_monomial_height_degree,
        'coordinate_dependent_witness_count': sum(tags[circuit.input_count:]),
        'constant_bounded_witness_count': len(tags) - circuit.input_count - sum(tags[circuit.input_count:]),
    }

def check_assignment(circuit, values, tags, weights, R, alpha, beta):
    check(len(values) == len(tags), 'assignment length')
    for i, value in enumerate(values):
        check(value <= weights[i] * (R + 1 if tags[i] else 1),
              'bound failure', i, value, tags[i], weights[i], R)
    explicit_limit = alpha * R + beta
    check(all(value <= explicit_limit for value in values[circuit.input_count:]),
          'explicit one-block bound failure', alpha, beta, R)
    return {
        'R': R,
        'explicit_height_limit': explicit_limit,
        'max_witness': max(values[circuit.input_count:], default=0),
        'total_witness_bits': sum(max(1, x.bit_length()) for x in values[circuit.input_count:]),
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True, help='Location of the source compiler packet')
    parser.add_argument('--output', type=Path, required=True, help='Receipt path outside both input packet and companion directory')
    parser.add_argument('--include-cascade', action='store_true')
    args = parser.parse_args()
    packet = args.packet.resolve()
    output = args.output.resolve()
    companion = Path(__file__).resolve().parent
    if output.is_relative_to(packet) or output.is_relative_to(companion):
        parser.error('--output must be external to both the input packet and companion directory')
    before = file_hashes(packet)
    sys.path.insert(0, str(packet))
    from compiler import Certificate, Circuit, Emitter, _parser, natural_pairs, sub, var
    fixtures = json.loads((packet / 'fixtures.json').read_text())
    sources = {k: v['data'] for k, v in fixtures['sources'].items()}
    cases = fixtures['cases']
    pairs = [(name, n) for name in sorted(sources) for n in (0, 1, 2, 3)]
    if args.include_cascade:
        pairs.append(('increment_right', 5))
    receipt = {
        'format': 'linear-witness-height-audit-v1',
        'optimized_python': not __debug__,
        'packet_reference': PACKET_REFERENCE,
        'input_sha256': before,
        'method': 'one-block natural-variable L1 majorant; at most one coordinate-dependent factor per assignment monomial',
        'block_audits': [],
        'endpoint_tests': [],
    }
    constants = {}
    for name, n in pairs:
        metadata = _parser.compile_lazy_source(sources[name])
        ell = n // 2
        K_E = n * (n - 1) // 2 * (4 * metadata.p + (14 * metadata.p + 2 * metadata.a) * max(n - 2, 0))
        K_P = n * (n - 1) // 2 * (4 * metadata.p + (8 * metadata.p + 2 * metadata.m) * max(n - 2, 0))
        P_E, P_P = (1 << (max(1, k) - 1).bit_length() for k in (K_E, K_P))
        b = metadata.B3
        H_star = 2 * (b + max(metadata.Z + metadata.J, 3 * b + 1))
        alpha = 14 + 12 * ell
        beta = ((10 + 6 * ell) * b + metadata.Z + metadata.J + 2 * H_star
                + n * (metadata.J + 1) + metadata.factors + P_E + P_P + 10)
        explicit_constants = dict(alpha=alpha, beta=beta, b=b, H_star=H_star,
                                  K_E=K_E, K_P=K_P, P_E=P_E, P_P=P_P,
                                  endpoint_type_count=metadata.factors)
        block_data = {}
        for block_name in ('E', 'P'):
            c = Circuit([f'x_{i}_{sign}' for i in range(n) for sign in ('p', 'm')])
            X = [sub(var(2 * i), var(2 * i + 1)) for i in range(n)]
            emitter = Emitter(c, metadata)
            emitter.block(X, block_name)
            tags, weights, report = audit_operations(c)
            report.update(source=name, n=n, block=block_name, tests=[], explicit_constants=explicit_constants)
            matching = [x['input'] for x in cases if x['source'] == name and x['mass'] == n]
            samples = matching[:2]
            if n == 5:
                samples.append(next(x['input'] for x in cases if x['id'] == 'malformed_cascade'))
            samples.extend(([i * 10**30 - 10**31 for i in range(n)],
                            [10**40 + i for i in range(n)],
                            [-10**40 + i for i in range(n)],
                            [0] * n))
            for X0 in samples:
                R = max(map(abs, X0), default=0)
                values = c.evaluate(natural_pairs(X0))
                report['tests'].append(check_assignment(c, values, tags, weights, R, alpha, beta))
            report['H_bits'] = report['H'].bit_length()
            block_data[block_name] = {'H': report['H'], 'w': report['witness_count']}
            receipt['block_audits'].append(report)
            print('passed', name, n, block_name, 'w=', report['witness_count'],
                  'H_bits=', report['H_bits'], flush=True)
            del emitter, c, tags, weights, values
            gc.collect()
        C = (4 * metadata.B3 + 1) * (alpha + beta)
        C_majorant = (4 * metadata.B3 + 1) * max(3, block_data['E']['H'], block_data['P']['H'])
        constants[name, n] = (C, C_majorant, block_data)

    # Full accepted endpoints, target-domain witnesses, horizon zero, either
    # direction, large translations, zero-particle and one-particle fibers.
    endpoint_specs = [('increment_right', n, T) for n, T in ((0, 0), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2))]
    endpoint_specs += [('direct', 2, 1), ('empty', 2, 1)]
    for name, n, T in endpoint_specs:
        C, C_majorant, blocks = constants[name, n]
        for inverse in (False, True):
            cert = Certificate(sources[name], n, T, inverse)
            expected_w = 4 * max(n - 1, 0) + T * (blocks['E']['w'] + blocks['P']['w'])
            check(cert.circuit.ledger()['witnesses'] == expected_w, 'witness count', name, n, T)
            base = [] if n == 0 else [-4] if n == 1 else [0, 5] if n == 2 else [0, 18, 19]
            for translation in (0, 10**40, -10**40):
                X0 = [x + translation for x in base]
                target = cert.result(X0)
                values = cert.witness(X0, target)
                aux = values[cert.circuit.input_count:]
                A = max(map(abs, X0), default=0)
                height_limit = C * (A + T + 1)
                check(all(v <= height_limit for v in aux), 'full bound', name, n, T, inverse)
                bits = sum(max(1, v.bit_length()) for v in aux)
                bit_limit = expected_w * max(1, height_limit.bit_length())
                check(bits <= bit_limit, 'bit bound')
                receipt['endpoint_tests'].append(dict(source=name, n=n, T=T,
                    inverse=inverse, translation=translation, A=A,
                    C=C, C_majorant=C_majorant, witness_count=expected_w,
                    max_witness=max(aux, default=0), height_limit=height_limit,
                    total_witness_bits=bits, bit_limit=bit_limit))
            del cert, values, aux
            gc.collect()
    after = file_hashes(packet)
    check(before == after, 'read-only packet inputs changed', before, after)
    receipt['input_sha256_unchanged'] = True
    receipt['summary'] = {
        'block_circuits_audited': len(receipt['block_audits']),
        'block_assignments_checked': sum(len(x['tests']) for x in receipt['block_audits']),
        'accepted_endpoint_assignments_checked': len(receipt['endpoint_tests']),
        'no_height_degree_two_assignment_monomials': True,
        'explicit_height_bounds_passed': True,
        'all_tests_passed': True,
    }
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt['summary'], sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
