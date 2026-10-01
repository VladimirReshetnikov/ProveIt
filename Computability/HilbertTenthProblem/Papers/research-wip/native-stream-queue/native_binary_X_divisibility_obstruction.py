"""Deleting q|X from the standalone binary selector admits q=48.

Exact source identities and finite valuation checks accompany a parametric
positive Pell extension. The enormous full Pell tuple is not materialized.
"""
import argparse
from collections import Counter
import json
from math import comb
from pathlib import Path

import sympy as sp
import native_controller_binary_selector56 as parent


def build():
    def sub(value):
        return {'wn2': 'bs_X_bound', 'n2': 'q'}.get(value, value)
    assert parent.CORE[0] == ('wn2', '*', 'w', 'n2')
    source = list(parent.OUTER) + list(parent.BOUND)
    source += [(n, op, sub(a), sub(b)) for n, op, a, b in parent.CORE[1:]]
    equalities = [('r', 'bs_packed'), ('bs_q', 'q'), ('s', 'bs_odd')]
    equalities += [(sub(a), sub(b)) for a, b in parent.CORE_EQUALITIES]
    aux = [n for n in parent.CORE_NAMES if n != 'w'] + ['odd_half', 'bound_beta']
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': 28, 'A': 27}
    assert len(source) == 55 and len(equalities) == 13 and len(aux) == 18
    return dict(source=source, comparisons=equalities, auxiliaries=aux,
                certificate_operations=55, multiplications=28,
                additions_subtractions=27, equations=13, positive_witnesses=18,
                SOS_operations=93, SOS_multiplications=41, SOS_additions_subtractions=52)


def source_check():
    packet = build()
    names = ['q', 'F0', 'F1', 'F2', 'F3'] + packet['auxiliaries']
    z = {n: sp.Symbol(n, positive=True) for n in names}
    env = parent.ternary.execute(packet['source'], z)
    lifted = dict(z, n2=z['q'], w=(z['r']+z['bound_beta'])/z['q'])
    before = parent.ternary.execute(parent.OUTER+parent.CORE+parent.BOUND, lifted)
    old_pairs = [('r', 'bs_packed'), ('bs_q', 'q'), ('s', 'bs_odd'),
                 ('bs_X_bound', 'wn2')] + parent.CORE_EQUALITIES
    old_residuals = [before[a]-before[b] for a, b in old_pairs]
    assert sp.expand(old_residuals[3]) == 0
    for (a, b), residual in zip(packet['comparisons'], old_residuals[:3]+old_residuals[4:]):
        assert sp.expand(env[a]-env[b]-residual) == 0
    return dict(packet=packet, exact_retained_residual_identities=13,
                deleted_bound_residual_identically_zero=True,
                scope='The formal lift uses rational w=X/q; integrality of this erased coordinate is precisely the lost condition.')


def factorial_valuation(n, p):
    out = 0
    while n:
        n //= p
        out += n
    return out


def counterexample():
    q, fields, r = 48, (17, 5, 23, 2), 274433
    assert sum(fields)+1 == q and parent.pack(q, fields) == r
    assert r == 2**18+2**13+2**12+1 and r % 2 == 1
    assert q**3+q*q+q+1 <= r < q**4
    central = comb(2*r, r)
    v2 = (central & -central).bit_length()-1
    v3 = factorial_valuation(2*r, 3)-2*factorial_valuation(r, 3)
    assert v2 == r.bit_count() == 4 and v3 == 7
    assert central % (3**7) == 0 and central % (3**8) != 0
    assert pow(2, 2*r+1, 3) == 2
    # X=-1 mod3. The alternating upper half of (1-1)^(2r)
    # equals central/2; this is the integer part Y modulo3.
    assert (central//2) % 3 == 0
    assert pow(2, 2*r+1, q) != 0
    assert q & (q-1)
    return dict(q=q, fields=list(fields), packed_r=r, binary_exponents=[0,12,13,18],
                central_bits=central.bit_length(), central_v2=v2, central_v3=v3,
                X_mod_q=pow(2,2*r+1,q), X_mod_3=2, Y_mod_3=0, Y_v2=4,
                Y_over_q_is_odd=True, q_is_power_of_two=False,
                full_Pell_tuple_materialized=False)


def small_identity_checks():
    cases = 0
    for r in range(1, 65):
        central = comb(2*r, r)
        alternating = sum((-1)**j*comb(2*r, r+j) for j in range(r+1))
        assert 2*alternating == central
        X = 2**(2*r+1)
        Y = sum(comb(2*r, r+j)*X**j for j in range(r+1))
        assert Y == (X+1)**(2*r)//X**r
        assert Y % 3 == (central//2) % 3
        assert (Y & -Y).bit_length()-1 == r.bit_count()
        cases += 1
    return dict(exact_rounding_alternating_half_and_valuation_cases=cases)


def verify():
    return dict(status='PASS_NATIVE_BINARY_X_DIVISIBILITY_OBSTRUCTION',
                source=source_check(), counterexample=counterexample(),
                identities=small_identity_checks(),
                scope='Rejects deleting q|X from the standalone selector56. Does not give a false input for a joined compiler whose q=16P^L imposes additional conditions.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--write', action='store_true')
    args=parser.parse_args(); result=json.loads(json.dumps(verify()))
    receipt=Path(__file__).with_suffix('.json')
    if args.write: receipt.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'])
