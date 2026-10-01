"""Keep89 operations and lower degree166 to162 using the strong unit first."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp

import complete75_norm_product89 as prior


RETAINED = prior.RETAINED
eliminated = prior.eliminated
FACTOR_NAMES = prior.FACTOR_NAMES
FACTOR_DEGREES = (26, 22, 42, 30, 9, 5, 22, 6)


def sources():
    original, certificate, comparisons, _ = prior.sources()
    nodes = {name: (op, left, right) for name, op, left, right in certificate}
    assert nodes['L17'] == ('*', 'ic22', 'aux_square_gap')
    nodes['L17'] = ('*', 'R16', 'aux_square_gap')
    certificate = prior.prior.ordered(nodes, comparisons)
    return original, certificate, comparisons, certificate+[('polynomial', '-', 'eight_units', 1)]


def source_checks():
    original, certificate, comparisons, polynomial = sources()
    _, previous, _, old_polynomial = prior.sources()
    old_nodes = {name: (op, left, right) for name, op, left, right in previous}
    new_nodes = {name: (op, left, right) for name, op, left, right in certificate}
    assert {name for name in old_nodes if old_nodes[name] != new_nodes[name]} == {'L17'}
    assert Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial) == {'M':48, 'A':41}
    rng = random.Random(8916201)
    totals = Counter()
    for case in range(512):
        signed = case >= 384
        supplied = {name: rng.randint(-12, 12) if signed else rng.randint(1, 12)
                    for name in RETAINED+['x']}
        if case % 3 == 0:
            supplied['zplus'] = 1
        if case % 127 == 0:
            supplied['Z'] = 10**80
        constants = dict(B=rng.choice((16, 32, 128, 512)), DC=3, DR=5, MC=2, MF=4,
                         cell_bits=5, inner_bits=3)
        inputs = eliminated.fixed_inputs({**supplied, **constants})
        env = eliminated.run(polynomial, inputs)
        old = eliminated.run(old_polynomial, inputs)
        r12 = old['ic22']-old['R16']
        gap = old['H17']**2-supplied['y_aux']**2
        factors = list(prior.manual_factors(supplied, constants))
        factors[3] -= r12*gap
        assert tuple(env[name] for name in FACTOR_NAMES) == tuple(factors)
        assert env['polynomial'] == prior.multiply(factors)-1
        remaining = prior.multiply(old[name] for name in FACTOR_NAMES if name != 'norm_aux')
        assert env['polynomial']-old['polynomial'] == -r12*gap*remaining
        restored = {'q': env['q'], 'r': env['r_lhs'], 'W': env['W'],
                    'ga': env['gamma_sum'], 'phi': env['R10a']-env['index_rhs'],
                    'zquot': supplied['zplus']-1,
                    **{name: env[register] for name, register in eliminated.DEFINITIONS.items()}}
        full = {**supplied, **restored, **constants,
                'alpha': supplied['alpha']+supplied['F']+supplied['Z']}
        old_full = eliminated.run(original, eliminated.fixed_inputs(full))
        residuals = [old_full[left]-old_full[right]
                     for left, right in eliminated.baseline.prior.EQUALITIES]
        expected = (1-residuals[5], 1+residuals[11], 1+residuals[17],
                    1+residuals[13]-residuals[12]*gap,
                    1+residuals[8], 1+residuals[2], 1+residuals[12], 1+residuals[14])
        assert tuple(factors) == expected
        assert env['polynomial'] == prior.multiply(expected)-1
        totals['signed_supplied_cases' if signed else 'positive_supplied_cases'] += 1
        totals['negative_computed_mu'] += env['exponent_rhs'] < 0
        totals['zero_restored_quotient'] += supplied['zplus'] == 1
    return dict(certificate=dict(operations=88, multiplications=48, additions_subtractions=40,
                                 witnesses=19, equations=1),
                polynomial=dict(operations=89, multiplications=48, additions_subtractions=41,
                                witnesses=19, exact_degree=162),
                comparisons=comparisons, polynomial_schedule=polynomial,
                changed_register='L17', assignment_counts=dict(totals),
                full_original19_identities=512, polynomial_difference_identities=512)


def highest_forms(v, B, d):
    forms = list(prior.highest_forms(v, B, d))
    Q = (B-1)*v['Jrep']
    k = v['eta']+v['zeta']
    forms[3] = v['f']**2*v['j']**2*k**2*v['w']**2*v['s']**4*Q**18
    return forms


def degree_checks():
    _, _, _, polynomial = sources()
    rng = random.Random(16289162)
    z = sp.Symbol('z')
    records = []
    for B, d in ((16, 4), (64, 6), (256, 8)):
        scales = {name: rng.randint(1, 7) for name in RETAINED+['x']}
        offsets = {name: rng.randint(0, 5) for name in scales}
        values = {name: sp.Poly(scales[name]*z+offsets[name], z) for name in scales}
        values.update(B=B, cell_bits=d, inner_bits=3, MC=2, MF=4, DC=3, DR=5)
        env = eliminated.run(polynomial, eliminated.fixed_inputs(values))
        factors = [sp.Poly(env[name], z) for name in FACTOR_NAMES]
        forms = highest_forms(scales, B, d)
        assert all(forms)
        assert tuple(p.degree() for p in factors) == FACTOR_DEGREES
        assert [p.LC() for p in factors] == forms
        out = sp.Poly(env['polynomial'], z)
        Ctop = (B-1)*scales['Jrep']-scales['F']-scales['Z']-scales['alpha']-2*d*scales['x']
        leading = (-32*(B-1)**105*scales['h']*(scales['rho']+scales['sigma'])
                   *scales['delta']**2*scales['i']**2*scales['f']**2*scales['j']**3
                   *(scales['eta']+scales['zeta'])**10*scales['w']**13
                   *scales['s']**22*scales['Jrep']**105*Ctop)
        assert out.degree() == 162 and out.LC() == leading == prior.multiply(forms)
        records.append(dict(B=B, cell_bits=d, scales=scales, offsets=offsets,
                            factor_degrees=FACTOR_DEGREES, degree=162,
                            leading_coefficient=str(leading)))
    return records


def reduction_lemma_checks():
    t, f, u, y, delta = sp.symbols('t f u y delta')
    K = delta*(f*f-1)
    old = t*t*(u*u-y*y)+y*y
    new = K*(u*u-y*y)+y*y
    assert sp.expand(new-old+(t*t-K)*(u*u-y*y)) == 0
    residues = []
    for A in range(4):
        for T in range(4):
            for F in range(4):
                value = (1+T*T-(A*A-1)*(F*F-1)) % 4
                assert value != 3
                residues.append((A,T,F,value))
    modified_cases = 0
    for A in range(4):
        for F in range(4):
            K = (A*A-1)*(F*F-1)
            assert K % 4 in (0,1)
            for U in range(4):
                for Y in range(4):
                    assert (K*(U*U-Y*Y)+Y*Y) % 4 != 3
                    modified_cases += 1
    return dict(symbolic_factor_difference=True, mod4_cases=len(residues),
                mod4_table=residues, modified_norm_mod4_cases=modified_cases,
                proof_scope='All integer zero sets; N4=1 is restored before substitution')


def verify():
    return dict(status='PASS_COMPLETE75_STRONG_REDUCTION89', source=source_checks(),
                degree=degree_checks(), reduction=reduction_lemma_checks(),
                established_complete_comparison_bound=75,
                limit='No gate-count improvement, no real-zero equivalence, no circuit optimum or formalization claim')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'], result['source']['polynomial'])
