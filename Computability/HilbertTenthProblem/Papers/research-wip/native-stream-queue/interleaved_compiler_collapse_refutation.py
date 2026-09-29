#!/usr/bin/env python3
"""Full false 74-operation positive split and 75-operation collapsed sources.

This is not either previously open 75-operation candidate. The witness
extension is parametric; finite examples materialize its complete outer block.
"""
from collections import Counter
from pathlib import Path
import argparse
import json
import sympy as sp
import explore_one_field_half_mask as half

BASE = half.baseline
CORE_NAMES = list(half.CORE_NAMES)
NAMES = ['n', 'V', 'Jrep'] + CORE_NAMES + [
    'C', 'alpha', 'P', 'v', 'zquot', 'W', 'kappa', 'mu', 'delta', 'phi', 'rho']
CONSTANTS = ['B', 'Q', 'm', 'DC', 'DR', 'cell_bits', 'inner_bits']
OUTER = [(name, op, 'V' if left == 'F' else left, 'V' if right == 'F' else right)
         for name, op, left, right in half.OUTER]
COLLAPSE = [
    ('bounded', '+', 'C', 'alpha'),
    ('Pv', '*', 'P', 'v'),
    ('K', '+', 'Kconstant', 'P'),
    ('BK', '*', 'B', 'K'),
    ('L', '+', 'BK', 1),
    ('LC', '*', 'L', 'C'),
    ('markedV', '+', 'V', 'W'),
    ('Bz', '*', 'B', 'zquot'),
    ('Bzqm1', '*', 'Bz', 'qm1'),
    ('transport_rhs', '+', 'markedV', 'Bzqm1'),
]
SCHEDULE = OUTER + half.CORE + COLLAPSE + BASE.ADAPTER
EQUALITIES = list(half.EQUALITIES) + [
    ('Pv', 'q'), ('LC', 'transport_rhs'), ('raw_bound', 'q')
] + BASE.EQUALITIES[15:]


def source_audit(collapsed):
    names = NAMES if collapsed else NAMES + ['Z', 'F']
    z = {name: sp.Symbol(name, positive=True, integer=True)
         for name in names + CONSTANTS + ['x']}
    split = [
        ('bounded', '+', 'C', 'alpha'), ('Pv', '*', 'P', 'v'),
        ('marked_rhs', '+', 'Z', 'W'), ('BF', '*', 'B', 'F'),
        ('V_rhs', '+', 'Z', 'BF'), ('K', '+', 'Kconstant', 'P'),
        ('KC', '*', 'K', 'C'), ('zqm1', '*', 'zquot', 'qm1'),
        ('transport_rhs', '+', 'F', 'zqm1'),
    ]
    schedule = SCHEDULE if collapsed else OUTER + half.CORE + split + BASE.ADAPTER
    equalities = EQUALITIES if collapsed else list(half.EQUALITIES) + [
        ('Pv', 'q'), ('C', 'marked_rhs'), ('V', 'V_rhs'),
        ('KC', 'transport_rhs'), ('raw_bound', 'q')
    ] + BASE.EQUALITIES[15:]
    initial = dict(z, Bm1=z['Q']-1,
                   Kconstant=z['DC']+z['Q']*z['DR'],
                   twice_cell_bits=4*z['cell_bits'])
    env = half.run(schedule, initial)
    module_z = dict(z, B=z['Q'], F=z['V'])
    sources = list(half.sources(module_z))
    q, a, C, V, W = z['n']**2, z['a'], z['C'], z['V'], z['W']
    D, H = (a+2)**2-1, 4*a+3
    u = 4*z['cell_bits']*z['x']+z['inner_bits']
    L = 1+z['B']*(z['DC']+z['Q']*z['DR']+z['P'])
    sources += [z['P']*z['v']-q]
    if collapsed:
        sources += [L*C-V-W-z['B']*z['zquot']*(q-1)]
    else:
        sources += [C-z['Z']-W, V-z['Z']-z['B']*z['F'],
                    (z['DC']+z['Q']*z['DR']+z['P'])*C-z['F']-z['zquot']*(q-1)]
    sources += [
        C+z['alpha']+4*z['cell_bits']*z['x']-q,
        z['kappa']-u-z['delta']*D,
        z['c']-z['kappa']-z['phi'],
        z['mu']**2-1-D*z['kappa']**2,
        z['mu']-W-a*z['kappa']-z['rho']*H,
    ]
    U = z['j']*z['c']-(2*z['r']+1)
    correction = sources[9]*(U**2-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(equalities, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if ix == 10 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, ix
        records.append(dict(index=ix, equality=[left, right], sign=sign))
    counts = Counter('M' if row[1] == '*' else 'A' for row in schedule)
    cost, multiplications, coordinates, equations = (75, 42, 31, 19) if collapsed else (74, 41, 33, 21)
    assert len(schedule) == cost and counts == {'M': multiplications, 'A': 33}
    assert len(names) == coordinates and len(set(names)) == coordinates
    assert len(equalities) == len(sources) == equations
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    assert sp.expand(env['odd_index']-u) == 0
    return dict(operations=cost, multiplications=multiplications, additions_subtractions=33,
                positive_coordinates=coordinates, equations=equations,
                ledger=dict(mask_module=51, transport_bound_stride=cost-65, input_bridge=14),
                schedule=[list(row) for row in schedule], source_checks=records,
                scope='Exact full source of a newly refuted interleaving candidate.')


def residue_subset(modulus, exponents, target):
    # Every 2^e is a unit for odd modulus. Proper S cannot be invariant
    # under adding a unit, so each new exponent strictly grows S.
    assert modulus % 2 == 1 and modulus > 1
    predecessors = {0: None}
    steps = 0
    for exponent in exponents:
        before = list(predecessors)
        weight = pow(2, exponent, modulus)
        for old in before:
            nxt = (old+weight) % modulus
            if nxt not in predecessors:
                predecessors[nxt] = (old, exponent)
        steps += 1
        assert len(predecessors) >= min(modulus, len(before)+1)
        if len(predecessors) == modulus:
            break
    assert len(predecessors) == modulus
    chosen = []
    residue = target % modulus
    while residue:
        residue, exponent = predecessors[residue]
        chosen.append(exponent)
    assert len(chosen) == len(set(chosen))
    value = sum(1 << exponent for exponent in chosen)
    assert value % modulus == target % modulus
    return value, steps


def subset_checks():
    cases = 0
    maximum_steps = 0
    for modulus in range(3, 64, 2):
        # Distinct, sparse exponent lists; no consecutive-power premise.
        for stride, offset in ((1, 0), (2, 1), (5, 3)):
            exponents = [offset+stride*j for j in range(modulus-1)]
            for target in range(modulus):
                _, steps = residue_subset(modulus, exponents, target)
                assert steps <= modulus-1
                maximum_steps = max(maximum_steps, steps)
                cases += 1
    return dict(targets=cases, odd_moduli=31, largest_modulus=63,
                maximum_steps=maximum_steps)


def outer_examples():
    records = []
    for B, MC, MF in ((8, 2, 6), (16, 12, 6), (16, 10, 10)):
        d, b, Q = B.bit_length()-1, 1, B*B
        m = MC+B*MF
        assert m % 2 == 0 and 0 < m < Q-1 and m.bit_count() == d
        DC, DR, h = 1, 1, 1
        P = Q**h
        L = 1+B*(DC+Q*DR+P)
        N = (L+d-1)//d+h+2
        n, q = B**N, Q**N
        J = (q-1)//(Q-1)
        M = m*J
        top_bit = 2*d*(N-1)
        fixed_word = 1+(1 << top_bit)
        assert fixed_word & M == 0
        allowed = [j for j in range(1, 2*d*N) if j != top_bit and not ((M >> j) & 1)]
        assert len(allowed) >= L-1
        for x in (1, 2, 3):
            u, scaled = 4*d*x+b, 4*d*x
            W = 1 << u
            subset, steps = residue_subset(L, allowed[:L-1], -W-B*(q-1)-fixed_word)
            V = fixed_word+subset
            numerator = V+W+B*(q-1)
            C, remainder = divmod(numerator, L)
            alpha, v, z = q-C-scaled, q//P, 1
            Z = C-W
            F, field_remainder = divmod(V+W-C, B)
            assert field_remainder == 0 and 0 < F < q//B and Z > 0
            assert C == Z+W and V == Z+B*F
            assert (DC+Q*DR+P)*C == F+z*(q-1)
            r = (q-V)*(q-1)+M
            assert remainder == 0 and min(C-W, alpha, v, z) > 0
            assert P*v == q and L*C == V+W+B*z*(q-1)
            assert C+alpha+scaled == q
            assert 0 < V < q and V & M == 0 and V % 2 == r % 2 == 1
            assert n*n == q and r.bit_count() == 3*d*N
            assert q <= r < q*q and n**3 < r*r
            assert u < 2*r+1 and 0 < W < C < q
            # Desired data typing is an additional property, absent from source.
            data_mask = (MC+B*(B-1))*J
            assert C & data_mask
            records.append(dict(B=B, MC=MC, MF=MF, N=N, x=x, L=L,
                                q_bits=q.bit_length(), subset_steps=steps,
                                V_bits=V.bit_length(), C_bits=C.bit_length(),
                                packed_index_bits=r.bit_length(),
                                packed_population=r.bit_count(),
                                positive_outer_source=True, positive_separate_Z_F=True, data_typing_false=True,
                                whole_kernel_materialized=False))
    return dict(examples=records,
                scope='Exact outer witnesses and all positive-converse hypotheses; '
                      'final Pell/input coordinates are supplied parametrically.')


def verify():
    return dict(status='PASS_FULL_INTERLEAVE74_AND75_REFUTATION',
                split_source=source_audit(False), collapsed_source=source_audit(True),
                residue_lemma=subset_checks(),
                outer=outer_examples(), established_complete_bound=76,
                scope='These newly proposed full74 and full75 sources admit every positive input '
                      'for every fixed admissible compiler; neither earlier open75 is refuted.')


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
    print('Split:', result['split_source']['operations'], 'Collapsed:', result['collapsed_source']['operations'])
    print(result['residue_lemma'])
    print(result['outer'])
