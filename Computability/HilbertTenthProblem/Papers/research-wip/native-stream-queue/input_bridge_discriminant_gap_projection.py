#!/usr/bin/env python3
"""Exact current-76 gap deletion and its two-coset discriminant projection.

No improved complete certificate is claimed. Default compares the saved receipt.
"""
from pathlib import Path
from collections import Counter
from math import gcd, lcm
import argparse
import json
import sys
import sympy as sp

VERIFICATION = Path(__file__).resolve().parents[2] / 'verification'
sys.path.insert(0, str(VERIFICATION))
import explore_fixed_raw_universal_76 as base


def source_check():
    schedule = [row for row in base.SCHEDULE if row[0] != 'pell_gap']
    pairs = [pair for pair in base.EQUALITIES if pair != ('c', 'pell_gap')]
    sources = [value for ix, value in enumerate(base.source_residuals()) if ix != 16]
    env = base.fixed_environment(base.SYM)
    base.previous.previous.previous.previous.bridge.baseline.run_schedule(schedule, env)
    U = base.SYM['j'] * base.SYM['c'] - (2 * base.SYM['r'] + 1)
    correction = sources[12] * (U**2 - base.SYM['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(pairs, sources)):
        actual = sp.expand(env[left] - env[right])
        adjust = correction if ix == 13 else 0
        sign = 1 if sp.expand(actual - source - adjust) == 0 else -1
        assert sp.expand(actual - sign * source - adjust) == 0
        records.append({'index': ix, 'comparison': [left, right], 'source_sign': sign})
    counts = Counter('M' if row[1] == '*' else 'A' for row in schedule)
    names = [name for name in base.NAMES if name != 'phi']
    assert len(schedule) == 75 and counts == {'M': 41, 'A': 34}
    assert len(names) == 29 and len(pairs) == len(sources) == 18
    assert all(base.SYM['phi'] not in source.free_symbols for source in sources)
    return {'operations': 75, 'multiplications': 41, 'additions_subtractions': 34,
            'positive_coordinates': len(names), 'equations': len(pairs),
            'removed_instruction': ['pell_gap', '+', 'kappa', 'phi'],
            'removed_comparison': ['c', 'pell_gap'], 'residual_checks': records,
            'scope': 'Exact source deletion only; full soundness remains open.'}


def order_two(H):
    value = 2 % H
    order = 1
    while value != 1:
        value = 2 * value % H
        order += 1
    return order


def finite_projection():
    periods = pairs = 0
    for a in range(2, 42, 2):
        A, D, H = a + 2, (a + 2)**2 - 1, 4 * a + 3
        T = order_two(H)
        g = gcd(2 * D, T)
        period = lcm(2 * D, T)
        us = range(1, min(D, 12), 2)
        observed = {u: set() for u in us}
        chi, psi, exponent = 1, 0, 1
        for v in range(period):
            assert psi == (v if v % 2 else A * v) % D
            if psi in observed:
                observed[psi].add(exponent)
            chi, psi = A * chi % D, (chi + A * psi) % D
            exponent = 2 * exponent % H
        for u in us:
            predicted = {pow(2, start + 2 * D * j, H)
                         for start in (u, A * u) for j in range(T // g)}
            assert observed[u] == predicted
            pairs += H - 1
        periods += period
    return {'even_parameters': 20, 'direct_modular_recurrence_steps': periods,
            'candidate_endpoint_comparisons': pairs,
            'scope': 'Finite corroboration of both parity branches of the proved projection.'}


def positive_examples():
    rows = []
    for a in (2, 4, 6, 8, 12):
        A, D, H = a + 2, (a + 2)**2 - 1, 4 * a + 3
        for u in (1, 3, 5):
            for branch, v in [('odd', u + 2 * D), ('even', A * u + 2 * D)]:
                W = pow(2, v, H)
                mu, kappa = base.previous.pell(A, v)
                delta, rem = divmod(kappa - u, D)
                assert rem == 0 and delta > 0
                rho, rem = divmod(mu - a * kappa - W, H)
                assert rem == 0 and rho > 0
                assert mu * mu == 1 + D * kappa * kappa
                rows.append({'a': a, 'u': u, 'branch': branch, 'index': v,
                             'endpoint': W, 'all_bridge_coordinates_positive': True})
    return {'examples': rows, 'scope': 'Actual finite bridge Pell tuples, not full kernels.'}


def large_bound_alias():
    # Proth's primality theorem applies: odd k < 2^n and the displayed
    # half-power is -1. This is a checked primality certificate, not BPSW.
    k, n, proth_base = 133, 600, 3
    p = (k << n) + 1
    assert k % 2 and k < (1 << n)
    assert pow(proth_base, (p - 1) // 2, p) == p - 1
    a = 3 * k * (1 << (n - 2))
    A, D, H = a + 2, (a + 2)**2 - 1, 4 * a + 3
    assert H == 3 * p and gcd(D, k) == 1
    q, J0, u, w, W = 16, 539, 5, 3, 8
    assert 0 < u < q < J0 < a and 2**J0 < a and 0 < W < q < H
    # An exponent annihilator of 2 modulo 3*p is N=p-1.
    N = p - 1
    assert pow(2, N, H) == 1 and gcd(2 * D, N) == 2
    # v=u+2D*t, v=w mod N. Its Pell tuple is supplied parametrically.
    t = ((w - u) // 2 * pow(D, -1, N // 2)) % (N // 2)
    v = u + 2 * D * t
    assert v > J0 and v % (2 * D) == u and v % N == w
    assert pow(2, v, H) == W and W != 2**u
    # Here T is even because 3 divides H. T divides N, so gcd(2D,T)=2.
    return {'k': k, 'n': n, 'proth_base': proth_base, 'prime_bits': p.bit_length(),
            'a_bits': a.bit_length(), 'q': q, 'main_index_bound': J0,
            'input_exponent': u, 'wrong_endpoint_exponent': w, 'endpoint': W,
            'lifted_pell_index_bits': v.bit_length(), 'gcd_2Delta_order_two': 2,
            'strict_bounds_verified': ['u<q<J0<a', '2^J0<a', '0<W<q<H'],
            'scope': 'Bridge counterexample with strong bounds and a certified parameter; '
                     'a is not claimed to have the actual packed-kernel shape.'}


def verify():
    return {'status': 'PASS_INPUT_BRIDGE_DISCRIMINANT_GAP_PROJECTION',
            'source': source_check(), 'finite_projection': finite_projection(),
            'positive_examples': positive_examples(), 'large_bound_alias': large_bound_alias(),
            'complete_bound_changed': False,
            'proof': 'input_bridge_discriminant_gap_projection.md'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print('75-operation deletion has an exact two-coset projection; full soundness is open.')
