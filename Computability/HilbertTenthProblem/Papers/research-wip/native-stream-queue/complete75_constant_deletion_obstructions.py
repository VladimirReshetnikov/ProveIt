"""Exact source audit of six empty 74-operation deletions from complete75.

The accompanying note proves emptiness; finite checks only corroborate the
explicit nonsquare, index-range and parity facts used in that proof.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

import sympy as sp

import complete75_half_binomial as baseline
import pell_kernel_half_binomial42 as kernel


# Remove the named gate and redirect every use to its indicated operand.
DELETIONS = {
    'first_norm_unit': ('R9', 'tau_square', 5),
    'main_norm_unit': ('R15', 'Ac2', 11),
    'auxiliary_norm_unit': ('f_square_minus_one', 'L16', 12),
    'input_norm_unit': ('norm_rhs', 'scaled_kappa2', 17),
    'first_index_successor': ('r1', 'r', 8),
    'input_odd_offset': ('odd_index', 'scaled_t', 15),
}


def independent_sources(z):
    q, C, J, F, alpha, Z, W = (z[n] for n in
                              ('q', 'C', 'Jrep', 'F', 'alpha', 'Z', 'W'))
    X, Y = z['w']*q**3, z['s']*q**3
    H = 4*z['a']+3
    D = z['a']**2+H
    u = 2*z['cell_bits']*z['x']+z['inner_bits']
    rho = z['i']*z['c']**2
    U = z['j']*z['c']-z['r']
    core = kernel.sources(dict(z, scale=q**3, R=z['r']))
    # Use the literal strong-square residual, independently of a preceding
    # equation. This avoids silently retaining its old norm substitution in
    # the auxiliary-unit deletion.
    core[8] = rho**2*(U**2-z['y_aux']**2)-1+z['y_aux']**2
    return [
        (z['B']-1)*J-q+1,
        C+alpha+2*z['cell_bits']*z['x']-q,
        (z['DC']+z['B']*z['DR']+X)*C-F-z['zquot']*(q-1),
        z['r']-(q*q-Z-q*F)*(q*q-1)
        -(z['MC']+q*(z['MF']+z['B']-1))*J,
        C-Z-W,
    ]+core+[
        z['kappa']-u-z['delta']*D,
        z['c']-z['kappa']-z['phi'],
        z['mu']**2-1-D*z['kappa']**2,
        z['mu']-W-z['a']*z['kappa']-z['rho']*H,
    ]


def source_audit():
    retained = baseline.source_audit()
    rows = retained['schedule']
    prior = baseline.prior
    z = prior.SYM
    original = independent_sources(z)
    D = z['a']**2+4*z['a']+3
    adjustments = {
        'first_norm_unit': -1,
        'main_norm_unit': 1,
        'auxiliary_norm_unit': -D,
        'input_norm_unit': 1,
        'first_index_successor': 1,
        'input_odd_offset': z['inner_bits'],
    }
    records = []
    for label, (removed, alias, changed) in DELETIONS.items():
        rename = lambda operand: alias if operand == removed else operand
        modified = [(name, op, rename(left), rename(right))
                    for name, op, left, right in rows if name != removed]
        comparisons = [(rename(left), rename(right))
                       for left, right in prior.EQUALITIES]
        env = prior.fixed_environment(z)
        env['MF'] = z['MF']+z['B']-1
        env = kernel.run(modified, env)
        expected = original.copy()
        expected[changed] += adjustments[label]
        signs = []
        for index, ((left, right), residual) in enumerate(zip(comparisons, expected)):
            actual = sp.expand(env[left]-env[right])
            sign = 1 if sp.expand(actual-residual) == 0 else -1
            assert sp.expand(actual-sign*residual) == 0, (label, index)
            signs.append(sign)
        counts = Counter(op for _, op, _, _ in modified)
        assert len(modified) == 74 and counts['*'] == 41
        assert counts['+']+counts['-'] == 33
        assert len(comparisons) == 19 and len(prior.NAMES) == 30
        assert removed not in env
        records.append(dict(
            deletion=label, removed_instruction=next(row for row in rows if row[0] == removed),
            redirected_to=alias, operations=74, multiplications=41,
            additions_subtractions=33, positive_witnesses=30, equations=19,
            changed_equation_index=changed, source_signs=signs,
            changed_residual=sp.sstr(sp.expand(expected[changed])),
            schedule=[list(row) for row in modified],
            comparisons=[list(pair) for pair in comparisons],
        ))
    return dict(baseline_operations=75, variants=records,
                independent_polynomials_checked=19*len(records),
                auxiliary_second_norm='Literal (i*c^2)^2*(U^2-y^2)-1+y^2; no residual correction needed')


def finite_lemmas():
    nonsquares = 0
    for a in range(1, 501):
        A = a+2
        D = a*a+4*a+3
        assert (A-1)**2 < D < A*A
        nonsquares += 1
    for V in range(1, 501):
        assert V*V < V*(V+1) < (V+1)**2
        assert (2*V+1)**2-4*V*(V+1) == 1
        nonsquares += 1

    ranges = 0
    for q in range(16, 81):
        for R in sorted({3*q+1, 3*q+2, q*q, q**4-1}):
            if not 3*q+1 <= R < q**4:
                continue
            X = Y = q**3
            E = X*Y
            a = Y*(X+1)
            A = a+2
            P = 2*X*Y*Y+1
            assert E > 2*R and a > R and P > A
            assert Y*R > 2*R
            n_min = (R+1)//2
            assert n_min+1 >= 6
            assert (2*A-1)**5 > A*(A*A-1)**2
            ranges += 1

    input_residues = 0
    for A in range(4, 82, 2):
        D = A*A-1
        for v in range(1, A-1):
            _, psi = kernel.binary.pell(A, v)
            representative = v if v % 2 else v*A
            assert psi % D == representative and 0 < representative < D
            # An even input u smaller than A cannot equal either branch.
            assert not any(representative == u for u in range(2, A, 2))
            input_residues += 1

    parity_lifts = 0
    for p in range(1, 81):
        for m in range(2*p, 2*p+7):
            for sign in (-1, 1):
                for lift in range(-2, 3):
                    s = sign*p+2*m*lift
                    assert s % 2 == p % 2
                    if s % 2 and p % 2 == 0:
                        raise AssertionError('impossible odd auxiliary lift')
                    parity_lifts += 1
    return dict(nonsquare_interval_cases=nonsquares,
                first_index_preparation_cases=ranges,
                input_discriminant_residues=input_residues,
                signed_index_parity_lifts=parity_lifts,
                scope='Finite checks of proof lemmas, not exhaustive positive-source search')


def verify():
    return dict(
        status='PASS_SIX_EMPTY_COMPLETE75_CONSTANT_DELETIONS',
        source=source_audit(), lemmas=finite_lemmas(),
        theorem='Each listed literal 74-operation variant has no strictly positive complete-source solution',
        established_complete_universal_bound=75,
        limits='Scoped mathematical obstruction with exact source audits; no general circuit lower bound, no smaller universal certificate, no formal proof',
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'], '6 variants;', result['source']['independent_polynomials_checked'],
          'independent source comparisons')
