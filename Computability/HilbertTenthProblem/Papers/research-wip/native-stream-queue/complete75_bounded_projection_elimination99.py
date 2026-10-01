"""A 99-operation universal polynomial with 19 positive witnesses.

The comparison certificate costs76. A canonical compiler margin permits
stronger raw slack; a shared linear factor saves one packing operation.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import sympy as sp

import complete75_signed_projection_elimination101 as signed


eliminated = signed.eliminated
compiler = signed.dominance.bounded.compiler
RETAINED = [name for name in signed.RETAINED if name != 'r']
DELETED_EQUALITIES = signed.DELETED_EQUALITIES | {3}


def sources():
    original, prior, pairs, indices = signed.sources()
    nodes = {name: (op, left, right) for name, op, left, right in prior}
    assert nodes.pop('C_partial') == ('-', 'q', 'alpha')
    assert nodes['marked_rhs'] == ('-', 'C_partial', 'scaled_t')
    assert nodes.pop('qF') == ('*', 'q', 'F')
    assert nodes.pop('packed') == ('+', 'Z', 'qF')
    assert nodes['gap'] == ('-', 'Lbig', 'packed')
    nodes.update(q_minus_F=('-', 'q', 'F'),
                 q_minus_FZ=('-', 'q_minus_F', 'Z'),
                 C_after_alpha=('-', 'q_minus_FZ', 'alpha'),
                 marked_rhs=('-', 'C_after_alpha', 'scaled_t'),
                 gap_product=('*', 'repunit', 'q_minus_F'),
                 gap=('+', 'gap_product', 'q_minus_FZ'))
    free = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    free.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    certificate = []
    active, done = set(), set(free)

    def visit(name):
        name = 'r_lhs' if name == 'r' else name
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
        if index != 3:
            comparisons.append(tuple(visit(name) for name in pair))
            retained_indices.append(index)
    assert len(certificate) == len(nodes) == 76
    assert len(comparisons) == 8 and len(RETAINED) == 19
    return original, certificate, comparisons, retained_indices


def verify_source():
    original, certificate, pairs, indices = sources()
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate) == {'M': 41, 'A': 35}
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial) == {'M': 49, 'A': 50}
    assert len(polynomial) == 99
    _, prior, oldpairs, oldindices = signed.sources()
    alias = lambda name: 'r_lhs' if name == 'r' else name
    expected = {name: (op, alias(left), alias(right)) for name, op, left, right in prior
                if name not in ('C_partial', 'marked_rhs', 'qF', 'packed', 'gap')}
    expected.update(q_minus_F=('-', 'q', 'F'),
                    q_minus_FZ=('-', 'q_minus_F', 'Z'),
                    C_after_alpha=('-', 'q_minus_FZ', 'alpha'),
                    marked_rhs=('-', 'C_after_alpha', 'scaled_t'),
                    gap_product=('*', 'repunit', 'q_minus_F'),
                    gap=('+', 'gap_product', 'q_minus_FZ'))
    assert {name: (op, left, right) for name, op, left, right in certificate} == expected
    assert list(zip(indices, pairs)) == [(index, tuple(alias(n) for n in pair))
                                        for index, pair in zip(oldindices, oldpairs) if index != 3]
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert 'r' not in available
    q, F, Z, alpha, scaled = sp.symbols('q F Z alpha scaled')
    T, V = q-F, q-F-Z
    assert sp.expand((q-1)*T+V-(q*q-Z-q*F)) == 0
    C = V-alpha-scaled
    assert sp.expand(C+alpha+F+Z+scaled-q) == 0

    rng = random.Random(75099)
    algebraic = conditioned = negative_R = negative_W = 0
    for ensure_C_positive in (False, True):
        for _ in range(128):
            supplied = {name: rng.randint(1, 9) for name in RETAINED+['x']}
            constants = dict(B=16, DC=3, DR=5, MC=10, MF=12,
                             cell_bits=5, inner_bits=3)
            if ensure_C_positive:
                supplied['Jrep'] = rng.randint(10, 20)
            else:
                # Exercise the signed computed-index branch off the zero set.
                supplied['F'] = rng.randint(1, 200)
            env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
            restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                        'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                        **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
            full = {**supplied, **restored, **constants,
                    'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
            old = eliminated.run(original, eliminated.fixed_inputs(full))
            residuals = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
            assert all(residuals[index] == 0 for index in DELETED_EQUALITIES)
            assert [env[left]-env[right] for left, right in pairs] == [residuals[index] for index in indices]
            assert env[output] == sum(value*value for value in residuals)
            assert env['gap'] == env['q']**2-supplied['Z']-env['q']*supplied['F']
            algebraic += 1
            negative_R += restored['r'] < 0
            negative_W += restored['W'] < 0
            if ensure_C_positive:
                assert restored['C'] > 0
                assert 0 < supplied['F'] < env['q'] and 0 < supplied['Z'] < env['q']
                assert env['q_minus_FZ'] > 0 and env['gap'] > 0 and restored['r'] > 0
                assert -env['q'] < restored['W'] < env['q']
                assert restored['mu'] > 0
                conditioned += 1
    assert negative_R and negative_W

    degrees = {name: 1 for name in RETAINED+['x']}
    degrees.update({name: 0 for name in eliminated.baseline.prior.CONSTANTS})
    degrees.update(Bm1=0, Kconstant=0, twice_cell_bits=0)
    for name, op, left, right in polynomial:
        a = 0 if isinstance(left, int) else degrees[left]
        b = 0 if isinstance(right, int) else degrees[right]
        degrees[name] = a+b if op == '*' else max(a, b)
    assert degrees['r_lhs'] == 4
    bounds = [degrees[f'residual_{i}'] for i in range(8)]
    assert bounds == [5, 26, 9, 26, 22, 34, 6, 50]
    a, H, v, z = sp.symbols('a H v z')
    assert sp.expand((a*z+v)**2-(a*a+H)*z*z-1
                     -(2*a*z*v+v*v-H*z*z-1)) == 0
    bounds[3], bounds[7] = 22, 42
    t = sp.Symbol('t')
    fixture = {name: sp.Poly(t, t) for name in RETAINED+['x']}
    fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
    expression = sp.Poly(env[output], t)
    assert expression.degree() == 84 and expression.LC() == 16*15**60
    return dict(certificate=dict(operations=76, multiplications=41,
                                 additions_subtractions=35, witnesses=19, equations=8),
                polynomial=dict(operations=99, multiplications=49,
                                additions_subtractions=50, witnesses=19, exact_degree=84,
                                output_register=output),
                positive_witnesses=RETAINED,
                retained_original_comparison_indices=indices,
                comparisons=pairs, polynomial_schedule=polynomial,
                algebraic_old_source_replays=algebraic,
                conditional_positive_packing_cases=conditioned,
                negative_computed_R_identity_cases=negative_R,
                negative_W_identity_cases=negative_W,
                local_symbolic_rewiring=dict(unchanged_gates_under_R_alias=70,
                                             replaced_gates=5, replacement_gates=6,
                                             exact_gap_identity=True, exact_old_bound_identity=True),
                residual_degree_bounds=bounds,
                highest_homogeneous_term='16*(B-1)^60*delta^4*w^10*s^10*Jrep^60')


def verify_compiler_margin():
    alphabets = [([(0,)*9, (1,)*9], 2),
                 ([compiler.baseline.previous.previous.previous.cyclic_window([1, 0, 0], i, 1)
                   for i in range(3)], 2),
                 (list(product(range(2), repeat=9))[:100], 2),
                 ([(0,)*9, (1,)*9, (2,)*9], 3),
                 (list(product(range(2), repeat=9))[:3], 2)]
    layouts = []
    for windows, alphabet in alphabets:
        cc = compiler.compile_windows(windows, alphabet)
        coefficients = Counter()
        for exponent in cc.positions:
            # Two copies of C plus one arbitrary whole-cell temporal word.
            # Independent all-one Boolean lanes dominate every low dummy subset.
            coefficients[exponent] += 3
            coefficients[exponent+cc.H] += 1
            for degree, coefficient in cc.DCpoly.items():
                coefficients[exponent+degree] += coefficient
        maximum = max(coefficients.values())
        assert max(coefficients) < cc.L
        assert cc.R >= 16
        assert maximum <= cc.unshifted_mass_bound+3 <= cc.R//4+1
        assert 3*maximum <= cc.R-1
        assert cc.extra_dummy in cc.positions and cc.extra_dummy not in cc.coeff
        layouts.append(dict(native_positions=len(cc.positions), radix_bits=cc.radix_bits,
                            cell_length=cc.L, largest_support=max(coefficients),
                            maximum_coefficient_bits=maximum.bit_length(),
                            high_correction=cc.high_correction,
                            twice_C_plus_F_digit_at_most_radix_quarter_plus_one=True,
                            all_low_dummy_subsets_covered=True))
    assert {item['high_correction'] for item in layouts} == {0, 1}
    for t in range(4, 1001):
        assert 2*t < 2**t
    return dict(layouts=layouts, tested_layouts=len(layouts), input_growth_cases=997,
                parametric_bound='C+Z+F<2C+F<q/3 and 2d*x<q/2, so new alpha>q/6',
                scope='Actual sparse compiler coefficient domination; canonical upper dummy bits zero, every low dummy subset covered')


def verify():
    return dict(status='PASS_COMPLETE75_BOUNDED_PROJECTION_ELIMINATION99',
                source=verify_source(), compiler_margin=verify_compiler_margin(),
                established_complete_comparison_bound=75,
                theorem='The fixed complete75 compiler has the same accepted ordinary inputs via a degree84 polynomial of cost99 in19 positive witnesses',
                limits='This76-operation certificate does not improve the75 comparison bound. Stronger raw slack preserves canonical completeness rather than every old witness; conditional positivity is proved on the zero set.')


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
