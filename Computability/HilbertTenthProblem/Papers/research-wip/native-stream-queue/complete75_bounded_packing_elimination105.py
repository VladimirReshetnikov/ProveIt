"""A 105-operation positive-witness polynomial using a stronger raw bound.

The arithmetic certificate costs 76 operations.  Its ten retained
comparisons give one polynomial in 21 positive witnesses, of degree84.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import sympy as sp

import complete75_positive_elimination as eliminated
import complete75_half_binomial_compiler as compiler


RETAINED = [name for name in eliminated.RETAINED if name != 'r']
DELETED_EQUALITIES = eliminated.DELETED_EQUALITIES | {3}


def sources():
    original, prior, pairs, indices = eliminated.sources()
    alias = lambda name: 'r_lhs' if name == 'r' else name
    certificate = []
    for name, op, left, right in prior:
        certificate.append((name, op, alias(left), alias(right)))
        if name == 'raw_bound':
            certificate.append(('strengthened_raw_bound', '+', 'raw_bound', 'F'))
    comparisons = []
    retained_indices = []
    for index, (left, right) in zip(indices, pairs):
        if index == 3:
            continue
        if index == 1:
            assert (left, right) == ('raw_bound', 'q')
            left = 'strengthened_raw_bound'
        comparisons.append((alias(left), alias(right)))
        retained_indices.append(index)
    assert len(certificate) == 76 and len(comparisons) == 10 and len(RETAINED) == 21
    return original, certificate, comparisons, retained_indices


def verify_source():
    original, certificate, pairs, indices = sources()
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    assert counts == {'M': 41, 'A': 35}
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == 105 and counts == {'M': 51, 'A': 54}

    # Local rewiring is exact, not a sampled polynomial identity: every
    # earlier gate is preserved under r -> r_lhs, plus the one bound gate.
    _, prior, _, _ = eliminated.sources()
    expected = {name: (op, 'r_lhs' if left == 'r' else left,
                       'r_lhs' if right == 'r' else right)
                for name, op, left, right in prior}
    expected['strengthened_raw_bound'] = ('+', 'raw_bound', 'F')
    assert {name: (op, left, right) for name, op, left, right in certificate} == expected
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available |= {'Bm1', 'Kconstant', 'twice_cell_bits'}
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert 'r' not in available

    rng = random.Random(75105)
    algebraic = positive = 0
    for enforce_bound in (False, True):
        for _ in range(128):
            supplied = {name: rng.randint(1, 9) for name in RETAINED+['x']}
            constants = dict(B=16, DC=3, DR=5, MC=10, MF=12,
                             cell_bits=5, inner_bits=3)
            if enforce_bound:
                supplied['Jrep'] = rng.randint(101, 150)
                q = 15*supplied['Jrep']+1
                supplied['alpha'] = (q-supplied['Z']-supplied['W']
                                     -supplied['F']-10*supplied['x'])
                assert supplied['alpha'] > 0
            env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
            restored = {'q': env['q'], 'r': env['r_lhs'],
                        **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
            # Restore the OLD bound slack, not the new coordinate with the
            # same source spelling.  This is crucial to soundness.
            full = {**supplied, **restored, **constants,
                    'alpha': supplied['alpha']+supplied['F']}
            old = eliminated.run(original, eliminated.fixed_inputs(full))
            residuals = [old[left]-old[right]
                         for left, right in eliminated.baseline.prior.EQUALITIES]
            assert all(residuals[index] == 0 for index in DELETED_EQUALITIES)
            assert [env[left]-env[right] for left, right in pairs] == [residuals[index] for index in indices]
            assert env[output] == sum(value*value for value in residuals)
            algebraic += 1
            if enforce_bound:
                q, Z, F = env['q'], supplied['Z'], supplied['F']
                assert env['strengthened_raw_bound'] == q
                assert 0 < Z < q and 0 < F < q
                assert q*q-Z-q*F >= 1
                assert all(value > 0 for value in restored.values())
                positive += 1

    # The eliminated R has degree four, below the jc term's degree six.
    # Therefore it changes no maximal residual degree.  P10 is untouched.
    residual_degrees = [1, 5, 26, 9, 22, 22, 34, 6, 17, 42]
    t = sp.Symbol('t')
    fixture = {name: sp.Poly(t, t) for name in RETAINED+['x']}
    fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    fixture_env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
    expression = sp.Poly(fixture_env[output], t)
    assert expression.degree() == 84 and expression.LC() == 16*15**60
    return dict(certificate=dict(operations=76, multiplications=41,
                                 additions_subtractions=35, witnesses=21, equations=10),
                polynomial=dict(operations=105, multiplications=51,
                                additions_subtractions=54, witnesses=21, exact_degree=84,
                                output_register=output),
                positive_witnesses=RETAINED,
                retained_original_comparison_indices=indices,
                comparisons=pairs, polynomial_schedule=polynomial,
                original_source_identity_checks=algebraic,
                bound_conditioned_positive_extension_checks=positive,
                unconditional_local_rewiring=True,
                residual_degree_bounds=residual_degrees,
                highest_homogeneous_term='16*(B-1)^60*delta^4*w^10*s^10*Jrep^60')


def verify_compiler_margin():
    alphabets = [([(0,)*9, (1,)*9], 2),
                 ([compiler.baseline.previous.previous.previous.cyclic_window([1,0,0], i, 1)
                   for i in range(3)], 2),
                 (list(product(range(2), repeat=9))[:100], 2),
                 ([(0,)*9, (1,)*9, (2,)*9], 3),
                 (list(product(range(2), repeat=9))[:3], 2)]
    layouts = []
    for windows, alphabet in alphabets:
        cc = compiler.compile_windows(windows, alphabet)
        # Dominate C+F with all old Boolean native positions turned on in
        # each independent lane.  This includes every allowed low dummy bit.
        # The extra upper dummy bits are zero in the canonical construction.
        coefficients = Counter()
        for exponent in cc.positions:
            coefficients[exponent] += 2  # C itself plus the temporal word.
            coefficients[exponent+cc.H] += 1
            for degree, coefficient in cc.DCpoly.items():
                coefficients[exponent+degree] += coefficient
        maximum = max(coefficients.values())
        assert max(coefficients) < cc.L
        assert maximum <= cc.unshifted_mass_bound+2 <= cc.R//4
        assert 3*maximum <= cc.R-1
        assert cc.extra_dummy in cc.positions and cc.extra_dummy not in cc.coeff
        layouts.append(dict(native_positions=len(cc.positions), radix_bits=cc.radix_bits,
                            cell_length=cc.L, largest_support=max(coefficients),
                            maximum_coefficient_bits=maximum.bit_length(),
                            high_correction=cc.high_correction,
                            combined_C_plus_F_digit_at_most_radix_quarter=True,
                            all_low_dummy_subsets_covered=True))
    assert {item['high_correction'] for item in layouts} == {0, 1}
    for t in range(4, 1001):
        assert 2*t < 2**t
    return dict(layouts=layouts, tested_layouts=len(layouts),
                input_growth_cases=997,
                parametric_bound='C+F<q/3 and 2d*x<d*N<q/2, so new alpha>q/6',
                scope='Exact sparse compiler coefficient domination; no full padded word or universal Pell tuple is materialized')


def verify():
    return dict(status='PASS_COMPLETE75_BOUNDED_PACKING_ELIMINATION105',
                source=verify_source(), compiler_margin=verify_compiler_margin(),
                established_comparison_certificate_bound=75,
                theorem='The fixed complete75 compiler gives an equivalent accepted input set via one polynomial of cost105 and degree84 in21 positive witnesses',
                limits='Stronger bound preserves canonical completeness, not every old witness; polynomial cost105 is distinct from certificate cost76; not an optimality or formal proof claim')


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
