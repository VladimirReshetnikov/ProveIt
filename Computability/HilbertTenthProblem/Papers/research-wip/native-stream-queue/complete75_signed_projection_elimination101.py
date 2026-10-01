"""A 101-operation universal polynomial with 20 positive witnesses.

The certificate still costs75. C and W are computed differences; their
positivity, and that of the input root and gap, is proved on the zero set.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_gamma_dominance_elimination102 as dominance


eliminated = dominance.eliminated
RETAINED = [name for name in dominance.PARETO_RETAINED if name != 'W']
DELETED_EQUALITIES = eliminated.DELETED_EQUALITIES | {1, 16}


def sources():
    original, prior, pairs, indices = eliminated.sources()
    prior, pairs, indices = dominance.gamma_rewire(prior, pairs, indices)
    nodes = {name: (op, left, right) for name, op, left, right in prior}
    assert nodes.pop('bounded') == ('+', 'marked_rhs', 'alpha')
    assert nodes.pop('raw_bound') == ('+', 'bounded', 'scaled_t')
    assert nodes['marked_rhs'] == ('+', 'Z', 'W')
    nodes['C_partial'] = ('-', 'q', 'alpha')
    nodes['marked_rhs'] = ('-', 'C_partial', 'scaled_t')
    nodes['W'] = ('-', 'marked_rhs', 'Z')
    free = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    certificate = []
    active, done = set(), set(free)

    def visit(name):
        if isinstance(name, int) or name in done:
            return name
        assert name not in active, ('cyclic definition', name)
        active.add(name)
        op, left, right = nodes[name]
        left, right = visit(left), visit(right)
        certificate.append((name, op, left, right))
        active.remove(name)
        done.add(name)
        return name

    comparisons, retained_indices = [], []
    for pair, index in zip(pairs, indices):
        if index != 1:
            comparisons.append(tuple(visit(name) for name in pair))
            retained_indices.append(index)
    assert len(certificate) == len(nodes) == 75
    assert len(comparisons) == 9 and len(RETAINED) == 20
    return original, certificate, comparisons, retained_indices


def verify_local_rewiring(certificate, pairs, indices):
    original, prior, oldpairs, oldindices = eliminated.sources()
    inherited = eliminated.verify_local_rewiring(original, prior, oldpairs, oldindices)
    prior, oldpairs, oldindices = dominance.gamma_rewire(prior, oldpairs, oldindices)
    oldmap = {name: (op, left, right) for name, op, left, right in prior}
    expected = {name: gate for name, gate in oldmap.items()
                if name not in ('marked_rhs', 'bounded', 'raw_bound')}
    expected.update(C_partial=('-', 'q', 'alpha'),
                    marked_rhs=('-', 'C_partial', 'scaled_t'),
                    W=('-', 'marked_rhs', 'Z'))
    assert {name: (op, left, right) for name, op, left, right in certificate} == expected
    assert list(zip(indices, pairs)) == [(i, p) for i, p in zip(oldindices, oldpairs) if i != 1]
    q, alpha, scaled, Z = sp.symbols('q alpha scaled Z')
    C = q-alpha-scaled
    W = C-Z
    assert sp.expand(C+alpha+scaled-q) == 0
    assert sp.expand(C-Z-W) == 0
    # These identities are unconditional, even when C or W is negative.
    return dict(inherited_positive_aliases=inherited,
                unchanged_gamma_only_gates=72, replaced_additions=3,
                replacement_subtractions=3, deleted_bound_is_identity=True,
                recovered_marker_is_identity=True,
                scope='Exact local gate comparison and polynomial identities on every assignment')


def verify_source():
    original, certificate, pairs, indices = sources()
    local = verify_local_rewiring(certificate, pairs, indices)
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate) == {'M': 41, 'A': 34}
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial) == {'M': 50, 'A': 51}
    assert len(polynomial) == 101
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert 'r' in RETAINED and 'W' not in RETAINED and 'W' in available
    assert not {'raw_bound', 'bounded', 'pell_gap', 'strengthened_raw_bound'} & available

    rng = random.Random(75101)
    negative_C = negative_W = 0
    for _ in range(256):
        supplied = {name: rng.randint(1, 9) for name in RETAINED+['x']}
        constants = dict(B=16, DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        restored = {'q': env['q'], 'W': env['W'], 'ga': env['gamma_sum'],
                    'phi': env['R10a']-env['index_rhs'],
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        old = eliminated.run(original, eliminated.fixed_inputs({**supplied, **restored, **constants}))
        residuals = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        assert all(residuals[index] == 0 for index in DELETED_EQUALITIES)
        assert [env[left]-env[right] for left, right in pairs] == [residuals[index] for index in indices]
        assert env[output] == sum(value*value for value in residuals)
        negative_C += restored['C'] < 0
        negative_W += restored['W'] < 0
    assert negative_C and negative_W

    degrees = {name: 1 for name in RETAINED+['x']}
    degrees.update({name: 0 for name in eliminated.baseline.prior.CONSTANTS})
    degrees.update(Bm1=0, Kconstant=0, twice_cell_bits=0)
    for name, op, left, right in polynomial:
        a = 0 if isinstance(left, int) else degrees[left]
        b = 0 if isinstance(right, int) else degrees[right]
        degrees[name] = a+b if op == '*' else max(a, b)
    bounds = [degrees[f'residual_{i}'] for i in range(9)]
    assert bounds == [5, 4, 26, 9, 26, 22, 34, 6, 50]
    a, H, v, z = sp.symbols('a H v z')
    assert sp.expand((a*z+v)**2-(a*a+H)*z*z-1
                     -(2*a*z*v+v*v-H*z*z-1)) == 0
    bounds[4] = 22
    bounds[8] = 42
    assert bounds == [5, 4, 26, 9, 22, 22, 34, 6, 42]
    # With fixed constants, the input norm has unique top part
    # -4*(B-1)^30*delta^2*w^5*s^5*Jrep^30 (degree42).
    # Its square is the unique degree84 part of the sum of squares.
    t = sp.Symbol('t')
    fixture = {name: sp.Poly(t, t) for name in RETAINED+['x']}
    fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
    expression = sp.Poly(env[output], t)
    assert expression.degree() == 84 and expression.LC() == 16*15**60
    return dict(certificate=dict(operations=75, multiplications=41,
                                 additions_subtractions=34, witnesses=20, equations=9),
                polynomial=dict(operations=101, multiplications=50,
                                additions_subtractions=51, witnesses=20, exact_degree=84,
                                output_register=output),
                positive_witnesses=RETAINED,
                retained_original_comparison_indices=indices,
                comparisons=pairs, polynomial_schedule=polynomial,
                algebraic_old_source_replays=256,
                negative_C_identity_cases=negative_C,
                negative_W_identity_cases=negative_W,
                local_symbolic_rewiring=local, residual_degree_bounds=bounds,
                highest_homogeneous_term='16*(B-1)^60*delta^4*w^10*s^10*Jrep^60')


def verify_pre_kernel_bounds():
    packing = signed = 0
    for B in (16, 32, 64):
        for J in range(1, 6):
            q = (B-1)*J+1
            for MC in (2, B-2):
                for MF in (4, B-4):
                    TC, TF = MC*J+1, MF*J-1
                    T = TC+q*TF
                    assert 0 < TC < q and 3 <= TF < q-2
                    assert 3*q+1 <= T < q*q-1
                    for F in range(1, q+2):
                        for Z in sorted({1, q-1, q, q*q-q*F+1, q*q-q*F+2}):
                            if Z <= 0:
                                continue
                            S = Z+q*F-1
                            R = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
                            assert R == (q*q-S)*(q*q-1)+T
                            if R <= 0:
                                assert S > q*q
                                continue
                            assert q <= S <= q*q
                            assert 1 <= Z <= q*q-q+1 < q*q
                            assert 3*q+1 <= R < q**4
                            for C in (1, q//2, q-1):
                                W = C-Z
                                assert -q*q < W < q
                                a = q**3*(q**3+1)
                                H, Delta = 4*a+3, a*a+4*a+3
                                kappa = 3+Delta
                                mu = W+a*kappa+H
                                assert a > q**6 and mu > 0
                                signed += W <= 0
                                packing += 1
    assert signed
    return dict(outer_bound_cases=packing, nonpositive_projection_cases=signed,
                scope='Pre-kernel implications on partial outer fixtures, not full accepting tuples')


def verify_input_recovery():
    residues = windows = signed_rejections = 0
    pell = dominance.kernel.binary.pell
    for A in range(4, 81):
        Delta = A*A-1
        for v in range(1, A-1):
            _, psi = pell(A, v)
            expected = v if v % 2 else v*A
            assert 0 < expected < Delta and psi % Delta == expected
            residues += 1
    for q in (16, 31, 32, 46, 64):
        for a in (q**6+1, q**6+q**3, 2*q**6):
            H = 4*a+3
            for u in range(3, a.bit_length(), 2):
                power = 2**u
                if power >= a:
                    continue
                assert -H < -q*q-power and q-power < H
                for shift in range(-2, 3):
                    W = power+shift*H
                    if -q*q < W < q:
                        assert shift == 0 and W == power and W > 0
                    else:
                        signed_rejections += W <= 0
                    windows += 1
    return dict(discriminant_residue_cases=residues,
                exponent_window_cases=windows,
                nonpositive_congruent_candidates_rejected=signed_rejections,
                scope='Exact index residue and signed representative-window checks')


def verify():
    return dict(status='PASS_COMPLETE75_SIGNED_PROJECTION_ELIMINATION101',
                source=verify_source(), pre_kernel_bounds=verify_pre_kernel_bounds(),
                input_recovery=verify_input_recovery(),
                gamma_dominance=dominance.verify_projection(),
                theorem='The fixed complete75 compiler has an equivalent degree84 polynomial of cost101 in20 positive witnesses and a75-operation comparison certificate with9 equations',
                limits='Computed C, W, mu and phi may be signed off the zero set; their positivity is proved on the zero set. Finite checks corroborate the proof and do not assert full huge Pell fixtures or formalization.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'], result['source']['certificate'], result['source']['polynomial'])
