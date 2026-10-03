"""A 102-operation polynomial with 20 positive witnesses and degree84.

Uses gamma=rho+sigma to imply the input Pell-index gap, while retaining
positive polynomial definitions of both Pell roots.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_bounded_packing_elimination105 as bounded
import pell_kernel_half_binomial42 as kernel


eliminated = bounded.eliminated
RETAINED = [name for name in bounded.RETAINED if name not in ('ga', 'phi')]+['sigma']
PARETO_RETAINED = [name for name in eliminated.RETAINED if name not in ('ga', 'phi')]+['sigma']
DELETED_EQUALITIES = bounded.DELETED_EQUALITIES | {16}


def gamma_rewire(prior, pairs, indices):
    certificate = []
    for name, op, left, right in prior:
        if name == 'pell_gap':
            assert (op, left, right) == ('+', 'index_rhs', 'phi')
            continue
        if name == 'gam':
            assert (op, left, right) == ('*', 'ga', 'a4m5')
            certificate.append(('gamma_sum', '+', 'rho', 'sigma'))
            left = 'gamma_sum'
        certificate.append((name, op, left, right))
    comparisons = [pair for pair, index in zip(pairs, indices) if index != 16]
    retained_indices = [index for index in indices if index != 16]
    return certificate, comparisons, retained_indices


def sources():
    original, prior, pairs, indices = bounded.sources()
    certificate, comparisons, retained_indices = gamma_rewire(prior, pairs, indices)
    assert len(certificate) == 76 and len(comparisons) == 9 and len(RETAINED) == 20
    return original, certificate, comparisons, retained_indices


def verify_pareto_alternative():
    original, prior, pairs, indices = eliminated.sources()
    certificate, pairs, indices = gamma_rewire(prior, pairs, indices)
    assert len(certificate) == 75 and len(pairs) == 10 and len(PARETO_RETAINED) == 21
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    assert counts == {'M': 41, 'A': 34}
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == 104 and counts == {'M': 51, 'A': 53}
    available = set(PARETO_RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available |= {'Bm1', 'Kconstant', 'twice_cell_bits'}
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert 'r' in PARETO_RETAINED and 'strengthened_raw_bound' not in available
    rng = random.Random(75104)
    deleted = eliminated.DELETED_EQUALITIES | {16}
    for _ in range(128):
        supplied = {name: rng.randint(1, 9) for name in PARETO_RETAINED+['x']}
        constants = dict(B=16, DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        restored = {'q': env['q'], 'ga': env['gamma_sum'],
                    'phi': env['R10a']-env['index_rhs'],
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        # Here alpha and the supplied positive R are unchanged.
        old = eliminated.run(original, eliminated.fixed_inputs({**supplied, **restored, **constants}))
        residuals = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        assert all(residuals[index] == 0 for index in deleted)
        assert [env[left]-env[right] for left, right in pairs] == [residuals[index] for index in indices]
        assert env[output] == sum(value*value for value in residuals)
    t = sp.Symbol('t')
    fixture = {name: sp.Poly(t, t) for name in PARETO_RETAINED+['x']}
    fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
    expression = sp.Poly(env[output], t)
    assert expression.degree() == 84 and expression.LC() == 16*15**60
    return dict(certificate=dict(operations=75, multiplications=41,
                                 additions_subtractions=34, witnesses=21, equations=10),
                polynomial=dict(operations=104, multiplications=51,
                                additions_subtractions=53, witnesses=21, exact_degree=84,
                                output_register=output),
                positive_witnesses=PARETO_RETAINED,
                retained_original_comparison_indices=indices,
                comparisons=pairs, polynomial_schedule=polynomial,
                algebraic_old_source_replays=128,
                residual_degree_bounds=[1, 5, 4, 26, 9, 22, 22, 34, 6, 42],
                scope='Gamma-dominance change alone, with original raw bound and supplied positive packed index')


def verify_source():
    original, certificate, pairs, indices = sources()
    polynomial, output = eliminated.polynomial_schedule(certificate, pairs)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in certificate)
    assert counts == {'M': 41, 'A': 35}
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert len(polynomial) == 102 and counts == {'M': 50, 'A': 52}
    available = set(RETAINED + eliminated.baseline.prior.CONSTANTS + ['x'])
    available |= {'Bm1', 'Kconstant', 'twice_cell_bits'}
    for name, _, left, right in polynomial:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    assert not {'r', 'ga', 'phi'} & available
    _, prior, _, _ = bounded.sources()
    oldmap = {name: (op, left, right) for name, op, left, right in prior}
    for name, op, left, right in certificate:
        if name == 'gamma_sum':
            assert (op, left, right) == ('+', 'rho', 'sigma')
        elif name == 'gam':
            assert (op, left, right) == ('*', 'gamma_sum', 'a4m5')
        else:
            assert (op, left, right) == oldmap[name]
    assert 'pell_gap' not in available

    rng = random.Random(75102)
    for _ in range(256):
        supplied = {name: rng.randint(1, 9) for name in RETAINED+['x']}
        constants = dict(B=16, DC=3, DR=5, MC=10, MF=12,
                         cell_bits=5, inner_bits=3)
        env = eliminated.run(polynomial, eliminated.fixed_inputs({**supplied, **constants}))
        restored = {'q': env['q'], 'r': env['r_lhs'], 'ga': env['gamma_sum'],
                    'phi': env['R10a']-env['index_rhs'],
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']}
        old = eliminated.run(original, eliminated.fixed_inputs(full))
        residuals = [old[left]-old[right] for left, right in eliminated.baseline.prior.EQUALITIES]
        assert all(residuals[index] == 0 for index in DELETED_EQUALITIES)
        assert [env[left]-env[right] for left, right in pairs] == [residuals[index] for index in indices]
        assert env[output] == sum(value*value for value in residuals)
        assert restored['ga'] > supplied['rho'] > 0
        # The restored phi and R are allowed to be signed in this identity
        # check. Their positivity is proved only on the full zero set.

    t = sp.Symbol('t')
    fixture = {name: sp.Poly(t, t) for name in RETAINED+['x']}
    fixture.update(B=16, DC=1, DR=1, MC=1, MF=1, cell_bits=5, inner_bits=3)
    env = eliminated.run(polynomial, eliminated.fixed_inputs(fixture))
    expression = sp.Poly(env[output], t)
    assert expression.degree() == 84 and expression.LC() == 16*15**60
    return dict(certificate=dict(operations=76, multiplications=41,
                                 additions_subtractions=35, witnesses=20, equations=9),
                polynomial=dict(operations=102, multiplications=50,
                                additions_subtractions=52, witnesses=20, exact_degree=84,
                                output_register=output),
                positive_witnesses=RETAINED,
                retained_original_comparison_indices=indices,
                comparisons=pairs, polynomial_schedule=polynomial,
                algebraic_old_source_replays=256,
                unconditional_local_rewiring=True,
                residual_degree_bounds=[1, 5, 26, 9, 22, 22, 34, 6, 42],
                highest_homogeneous_term='16*(B-1)^60*delta^4*w^10*s^10*Jrep^60')


def verify_projection():
    monotone = growth = fixtures = 0
    for A in range(2, 81):
        a = A-2
        previous = 1
        for u in range(1, 20):
            chi, psi = kernel.binary.pell(A, u)
            E = chi-a*psi
            assert E > previous
            previous = E
            monotone += 1
            _, psi2 = kernel.binary.pell(A, u+2)
            assert psi2-2*psi > A
            growth += 1
    examples = []
    for u in (3, 5, 7, 9, 11):
        for R in range(u+2, u+9, 2):
            if R % 4 != 3:
                continue
            X, W = 2**R, 2**u
            for a in (X+2, 2*X+4, 8*X):
                A, H = a+2, 4*a+3
                Delta = A*A-1
                D, c = kernel.binary.pell(A, R)
                mu, kappa = kernel.binary.pell(A, u)
                gamma, rem_main = divmod(D-X-a*c, H)
                rho, rem_input = divmod(mu-W-a*kappa, H)
                delta, rem_index = divmod(kappa-u, Delta)
                sigma, phi = gamma-rho, c-kappa
                assert rem_main == rem_input == rem_index == 0
                assert min(gamma, rho, delta, sigma, phi) > 0
                assert D == X+a*c+(rho+sigma)*H
                assert mu == W+a*kappa+rho*H
                assert mu-a*kappa < D-a*c
                assert D-a*c-(mu-a*kappa) > A > X
                assert D*D == 1+Delta*c*c
                assert mu*mu == 1+Delta*kappa*kappa
                fixtures += 1
                if len(examples) < 3:
                    examples.append(dict(u=u, R=R, a=a, sigma_positive=True, phi_positive=True))
    return dict(monotonicity_cases=monotone, two_step_growth_cases=growth,
                exact_positive_projection_fixtures=fixtures, examples=examples,
                scope='Main/input Pell interface fixtures; not full binomial or compiler tuples')


def verify():
    return dict(status='PASS_COMPLETE75_SHARED_PROJECTION_ELIMINATION102',
                source=verify_source(), projection=verify_projection(),
                pareto_alternative=verify_pareto_alternative(),
                compiler_margin=bounded.verify_compiler_margin(),
                established_comparison_certificate_bound=75,
                theorem='One fixed-compiler polynomial of cost102 and degree84 in20 positive witnesses represents every recursively enumerable set of positive ordinary inputs',
                limits='Certificate cost76 differs from polynomial evaluation102; conditional positivity of eliminated R and phi is proved on the zero set; not an optimality or formal proof claim')


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
