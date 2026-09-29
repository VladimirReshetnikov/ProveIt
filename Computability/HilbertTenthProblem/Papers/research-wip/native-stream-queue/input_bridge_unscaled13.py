#!/usr/bin/env python3
"""A conditional 13-operation unscaled bridge and its exact positive boundary."""
from collections import Counter
from pathlib import Path
import argparse
import json
import sys
import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent/'verification'))
from explore_fixed_raw_universal_77 import pell

SCHEDULE = [
    ('modulus', '+', 'a', 1),
    ('raw_bound', '+', 'bounded', 'x'),
    ('index_product', '*', 'delta', 'modulus'),
    ('index_rhs', '+', 'x', 'index_product'),
    ('gap', '+', 'kappa', 'phi'),
    ('kappa2', '*', 'kappa', 'kappa'),
    ('scaled_kappa2', '*', 'Delta', 'kappa2'),
    ('norm_rhs', '+', 'scaled_kappa2', 1),
    ('mu2', '*', 'mu', 'mu'),
    ('modulus_multiple', '*', 'rho', 'H'),
    ('difference_multiple', '*', 'a', 'kappa'),
    ('exponent_partial', '+', 'W', 'difference_multiple'),
    ('exponent_rhs', '+', 'exponent_partial', 'modulus_multiple'),
]
PAIRS = [('raw_bound', 'q'), ('kappa', 'index_rhs'), ('c', 'gap'),
         ('mu2', 'norm_rhs'), ('mu', 'exponent_rhs')]


def source_audit():
    z = {name: sp.Symbol(name, positive=True, integer=True) for name in
         ('a', 'q', 'c', 'C', 'alpha', 'x', 'W', 'kappa', 'phi', 'delta', 'mu', 'rho')}
    D, H = (z['a']+2)**2-1, 4*z['a']+3
    # These three registers were paid by the containing kernel/outer source.
    env = dict(z, Delta=D, H=H, bounded=z['C']+z['alpha'])
    for name, op, left, right in SCHEDULE:
        lhs = env[left] if isinstance(left, str) else left
        rhs = env[right] if isinstance(right, str) else right
        env[name] = lhs*rhs if op == '*' else lhs+rhs
    sources = [
        z['C']+z['alpha']+z['x']-z['q'],
        z['kappa']-z['x']-z['delta']*(z['a']+1),
        z['c']-z['kappa']-z['phi'],
        z['mu']**2-1-D*z['kappa']**2,
        z['mu']-z['W']-z['a']*z['kappa']-z['rho']*H,
    ]
    for (left, right), source in zip(PAIRS, sources):
        assert sp.expand(env[left]-env[right]-source) == 0
    counts = Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE) == 13 and counts == {'+': 7, '*': 6}
    failure = sp.expand(sources[1].subs({z['x']: 1, z['kappa']: 1}))
    assert sp.expand(failure+z['delta']*(z['a']+1)) == 0
    return dict(operations=13, multiplications=6, additions=7, equations=5,
                schedule=[list(row) for row in SCHEDULE], comparisons=[list(pair) for pair in PAIRS],
                borrowed_paid_registers=['Delta=(a+2)^2-1', 'H=4a+3', 'bounded=C+alpha'],
                x1_index_residual=str(failure), complete_universal_source=False)


def finite_pell_checks():
    rows = []
    for q in (16, 32, 64):
        a, J0 = 1 << (q+1), q+3
        A, D, H, M = a+2, (a+2)**2-1, 4*a+3, a+1
        _, c = pell(A, J0)
        assert q < J0 < M and 2**q < a
        for x in range(1, 7):
            W, C = 1 << x, (1 << x)+1
            alpha = q-C-x
            if alpha <= 0:
                continue
            mu, kappa = pell(A, x)
            delta, drem = divmod(kappa-x, M)
            rho, rrem = divmod(mu-a*kappa-W, H)
            phi = c-kappa
            assert drem == rrem == 0 and phi > 0
            assert mu*mu == 1+D*kappa*kappa
            assert kappa == x+delta*M and mu == W+a*kappa+rho*H
            if x == 1:
                assert kappa == 1 and mu == A and delta == rho == 0
            else:
                assert min(delta, rho, phi, kappa, mu, W) > 0
            rows.append(dict(q=q, x=x, W=W, positive_gap=True,
                             delta_positive=delta>0, rho_positive=rho>0,
                             all_five_equations=True, permitted_positive_bridge=x>=2))
    # Independent modular index formula, including both index parities.
    congruences = 0
    for a in range(1, 25):
        A, M = a+2, a+1
        for v in range(1, M):
            _, psi = pell(A, v)
            assert psi % M == v % M
            congruences += 1
    return dict(examples=rows, bounded_index_congruences=congruences,
                fixture_parameters='a=2^(q+1), J0=q+3; hence 2^q<a but 2^J0=4a>a.',
                scope='Tuples for the weaker conditional bridge interface only; '
                      'not actual main-kernel or complete compiler witnesses.')


def phase_checks():
    covered = uncovered = full_zero_masks = 0
    for d in range(1, 9):
        B = 1 << d
        for end_set in range(B):
            phases = [j for j in range(d) if (end_set >> j) & 1]
            if len(phases) == d:
                covered += 1
                for N in (1, 2, 3):
                    q, J = B**N, (B**N-1)//(B-1)
                    mask = end_set*J
                    assert mask == q-1
                    for Z in {1, q//2, q-1}:
                        assert Z & mask
                    full_zero_masks += 1
            else:
                j = next(j for j in range(d) if not ((end_set >> j) & 1))
                x = j+3*d
                assert x > 0 and x % d == j
                assert not ((end_set >> (x % d)) & 1)
                uncovered += 1
    return dict(full_phase_sets=covered, partial_sets_with_missing_input_phase=uncovered,
                full_mask_zero_remainder_checks=full_zero_masks,
                scope='Only periodic disjoint single-bit End insertion; no general compiler lower bound.')


def verify():
    return dict(status='PASS_CONDITIONAL_UNSCALED13_BRIDGE_BOUNDARY',
                source=source_audit(), pell=finite_pell_checks(), phases=phase_checks(),
                established_complete_bound=76,
                scope='Exact conditional bridge for x>=2; literal x=1 impossible; '
                      'all-phase fixed disjoint End variants exhaust the data field.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print(result['source']['operations'], result['source']['multiplications'], result['source']['additions'])
    print(result['phases'])
