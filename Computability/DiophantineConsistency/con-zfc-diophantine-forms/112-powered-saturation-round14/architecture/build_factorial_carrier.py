#!/usr/bin/env python3
"""One shared factorial for Horn-flow weights and reciprocal CRT moduli.

A ninth local coordinate bounds every possible rule label by the padded
horizon. This replaces the old enormous polynomial-coefficient carrier.
"""
from pathlib import Path
import argparse, hashlib, json
from math import factorial
import build_hybrid as h

ONE, TWO, const, bp = h.ONE, h.TWO, h.const, h.bp
LOCAL_NAMES = ('a', 'b', 'c', 'd', 'S', 'Sp', 'u', 'vq', 'w')

def projected_source(b, source, env, index):
    data = bp.codes(b, source, env)
    cs, I, A = data['codes'], data['I'], data['A']
    a, z, c, d = [env[s] for s in ('a', 'b', 'c', 'd')]
    add, mul, sd, sq = b.add, b.mul, b.sqdiff, b.square
    S, Sp, F = env['S'], env['Sp'], env['F']
    SpF = mul(Sp, F)
    ordinary = [sd(Sp, S)] + [sd(add(Sp, mul(SpF, code)), S) for code in cs[:-1]]
    guard = sd(mul(sd(c, a), sd(c, z)), sq(add(d, ONE)))
    bundle = add(sd(add(Sp, mul(SpF, cs[-1])), S), guard)
    def weight(v):
        return add(ONE, mul(v, F))
    implication, universal = I(a, z), A(a, z)
    mp = sd(mul(Sp, weight(z)), b.product([S, weight(a), weight(implication)]))
    gen = sd(mul(Sp, weight(universal)), mul(S, weight(z)))
    horn = b.product(ordinary + [bundle, mp, gen])
    den = add(mul(add(index, ONE), env['y']), ONE)
    beta = [sd(env['x'], add(S, mul(den, env['u']))),
            sd(env['x'], add(Sp, mul(add(den, env['y']), env['vq'])))]
    bound = b.sum(cs + [a, z, implication, universal, ONE])
    label_bound = sd(env['t'], add(env['w'], bound))
    return b.sum([horn] + beta + [label_bound])

def majorant(source):
    b = bp.UpperBuilder(True)
    atoms = {n: b.new(n) for n in ('t', 'x', 'y', 'F')}
    bounds = {n: atoms['t'] if n in ('a', 'b', 'c', 'd', 'w') else
              atoms['y'] if n in ('S', 'Sp') else atoms['x'] for n in LOCAL_NAMES}
    value = projected_source(b, source, atoms | bounds, atoms['t'])
    out = b.sum([value, atoms['t'], atoms['x'], atoms['y'], ONE])
    cert = bp.bound_certificate(b, atoms, out)
    cert['base'] = '2+t+x+y+F'
    cert['squared_difference_majorization'] = '(u-v)^2 <= (U+V)^2'
    cert['emitted_exponent'] = max(4, 1 << (cert['exponent'] - 1).bit_length())
    return cert

def construct(syntax='cantor', horizon_minimum=16):
    bp.ng.direct_source = h.CANTOR_SOURCE
    if syntax != 'cantor':
        h.shell_source.SHELL_SCHEME = syntax
        bp.ng.direct_source = h.shell_source.direct_source
    b = h.HybridBuilder(positive_powers=True)
    sourcebytes = (bp.ng.UP / 'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source = json.loads(sourcebytes)
    t = b.add(b.new('t0', 'outer'), const(horizon_minimum))
    x, y = [b.new(n, 'outer') for n in ('x', 'y')]
    F = b.factorial(t)
    params = {'t': t, 'x': x, 'y': y, 'F': F}
    u0, r0, ut = [b.new('endpoint.' + n) for n in ('u0', 'r0', 'ut')]
    dt = b.add(b.mul(b.add(t, ONE), y), ONE)
    b.eq(x, b.sum([F, ONE, b.mul(b.add(y, ONE), u0)]), 'endpoint.first_quotient')
    b.eq(y, b.sum([F, r0, ONE]), 'endpoint.first_remainder')
    b.eq(x, b.add(ONE, b.mul(dt, ut)), 'endpoint.last_quotient')
    bounds = {n: t if n in ('a', 'b', 'c', 'd', 'w') else
              y if n in ('S', 'Sp') else x for n in LOCAL_NAMES}
    encoded = {n: b.add(b.new('crt.encoded.' + n), ONE) for n in LOCAL_NAMES}
    C = b.add(b.new('crt.encoded_index_minus_one'), ONE)
    bc = majorant(source)
    E = bc['emitted_exponent']
    floor_exponent = factorial(horizon_minimum).bit_length()-1
    if E * floor_exponent >= 1 << floor_exponent or 2*E > 1 << floor_exponent:
        raise ValueError('padded-factorial carrier bound requires reproof')
    R = b.sum([TWO, t, x, y, F])
    K = b.mul(TWO, R)
    B = b.moduli_product(t, F)
    T = b.product_data['square']
    N = b.power(B, K)
    b.amplification_data = {'B': B, 'K': K, 'N': N, 'F': F, 't': t, 'R': R,
                           'local_degree_bound': E, 'budget': '2R',
                           'carrier_budget_lemma': {'horizon_minimum': horizon_minimum,
                               'floor_exponent': floor_exponent,
                               'exact_factorial_floor': factorial(horizon_minimum),
                               'checked': '2^floor_exponent>floor_exponent*E; 2^floor_exponent>=2E'},
                           'index': C, 'index_precision': 'K', 'completeness_precision': '2K'}
    for n in LOCAL_NAMES:
        b.divisible_binomial(encoded[n], b.add(bounds[n], ONE), N, 'crt.range.' + n)
    b.divisible_binomial(C, t, N, 'crt.range.index')
    iq = b.new('crt.index_quotient')
    b.eq(b.sum([C, T, ONE]), b.mul(B, iq), 'crt.reciprocal_index_congruence')
    value = projected_source(b, source, params | encoded, C)
    quotient = b.new('crt.nonnegative_quotient')
    b.eq(value, b.mul(N, quotient), 'crt.nonnegative_evaluation')
    b.finalize_binomials()
    b.finalize_power_frame()
    return b, sourcebytes, bc

def generate(out, syntax='cantor', horizon_minimum=16):
    out = Path(out)
    b, src, bc = construct(syntax, horizon_minimum)
    eq, poly, metrics = b.export(hashlib.sha256(src).hexdigest(), 'factorial_carrier_reciprocal_prime_power_' + syntax, True)
    meta = {'powers': [{'base': n, 'exponent': k, 'output': v} for (n, k), v in b.powers.items()],
            'factorials': b.factorial_certificates,
            'binomials': [{'n': n, 'k': k, 'output': v} for (n, k), v in b.binomials.items()],
            'ranges': b.range_requests, 'radix': b.radix_data, 'product': b.product_data,
            'amplification': b.amplification_data,
            'scale': b.shared_parameters, 'auxiliary': b.common_index_parameters,
            'discriminant': b.pell_D, 'derivations': b.index_derivations,
            'seeds': [{'exponent': k, 'pair': v} for k, v in b.seed_indices.items()],
            'indices': [{'exponent': k, 'pair': v} for k, v in b.shared_indices.items()],
            'variables': b.variables, 'rows': b.rows, 'gates': b.gates,
            'local_majorant': bc, 'syntax': syntax, 'local_names': LOCAL_NAMES,
            'wire_eliminated_source_sha256': eq['wire_eliminated_source_sha256']}
    # These two extra files retain the prime-power signed adapter's input API.
    for filename, obj in [('equation.json', eq), ('expanded_polynomial.json', poly),
                          ('METRICS.json', metrics), ('raw_audit_input.json', meta),
                          ('macro_inventory.json', b.macro_log),
                          ('gate_ledger.json', {'all_variables': b.variables, 'all_rows': b.rows, 'gates': b.gates}),
                          ('local_majorant.json', bc)]:
        h.write(out / 'raw' / filename, obj)
    target, cert, expanded = h.psd.contract(eq, support_cap=64)
    receipt, independent = h.check.verify(eq, target, cert)
    if expanded['terms'] != independent:
        raise ValueError('independent polynomial mismatch')
    for filename, obj in [('equation.json', target), ('elimination_certificate.json', cert),
                          ('expanded_polynomial.json', expanded), ('VERIFICATION.json', receipt)]:
        h.write(out / 'natural' / filename, obj)
    counts = {'source': metrics, 'natural': receipt, 'syntax': syntax,
              'power_calls': len(b.powers), 'seed_indices': len(b.seed_indices),
              'derived_indices': len(b.index_derivations), 'exact_binomials': len(b.binomials),
              'range_binomials': len(b.range_requests), 'factorials': len(b.factorials),
              'local_degree_bound': bc['emitted_exponent'], 'horizon_minimum': horizon_minimum}
    h.write(out / 'SUMMARY.json', counts)
    return counts

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--syntax', choices=['cantor', 'xx0', 'xy0'], default='cantor')
    p.add_argument('--horizon-minimum', type=int, default=16)
    a = p.parse_args()
    print(json.dumps(generate(a.output, a.syntax, a.horizon_minimum), indent=2))
