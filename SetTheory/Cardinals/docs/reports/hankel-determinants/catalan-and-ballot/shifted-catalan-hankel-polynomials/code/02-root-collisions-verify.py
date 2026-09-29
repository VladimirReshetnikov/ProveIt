#!/usr/bin/env python3
"""Run the exact verification suite and regenerate all shipped numerical data.

Use Python 3.10+, standard library only. The universal theorem is proved in
article.tex; these finite checks audit signs, constants, indexing and examples.
"""
from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path

from catalan_collisions import (
    Root, characteristic, christoffel_values, direct_hankel, fit_sectors,
    jets, minimal_recurrence, multiplier, peval, pmul,
    recurrence_residuals, sectors, sharp_order_bound,
    multiplicity_profile, recurrence_from_coefficients,
    determinant, secondary_hankel_formula,
)


def require(condition: bool, message: str) -> None:
    """Checks stay enabled even under python -O."""
    if not condition:
        raise AssertionError(message)


def encode_roots(roots: list[Root]) -> list[dict]:
    return [{'value': str(r.value), 'multiplicity': r.multiplicity} for r in roots]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('data'))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    counts: Counter = Counter()

    # Endpoint jets: the recurrence implementation does not use these formulas.
    for c in (0, 4):
        table = jets(c, 8, 18)
        for n in range(19):
            for r in range(8):
                b = F(comb(n+r, 2*r)) if n >= r else F(0)
                expected = ((-1)**(n-r)*b if c == 0
                            else F(2*n+1, 2*r+1)*b)
                require(table[n][r] == expected, f'endpoint jet {(c,n,r)}')
                counts['endpoint_jet_identities'] += 1

    # Independent original moment determinants, including signed, interior,
    # endpoint, multiple-root and constant multipliers.
    root_cases: list[list[Root]] = []
    for c in (-2, 0, 1, 2, 3, 4, 6):
        root_cases.extend([Root(c,t)] for t in range(1,6))
    for m, ell in product(range(4), repeat=2):
        root_cases.append(([Root(0,m)] if m else []) +
                          ([Root(4,ell)] if ell else []))
    for c,d in combinations((-1,0,2,4,6),2):
        for t,u in product((1,2),repeat=2):
            root_cases.append([Root(c,t),Root(d,u)])
    for m,ell,t in product((1,2),(1,2),(1,2,3)):
        root_cases.append([Root(0,m),Root(4,ell),Root(F(9,2),t)])
    for ts in product((1,2),repeat=3):
        root_cases.append([Root(c,t) for c,t in zip((1,2,3),ts)])
    for case_no, roots in enumerate(root_cases):
        for leading in (1,-2):
            coefficients = multiplier(roots,leading)
            values = christoffel_values(roots,leading,7)
            for n, value in enumerate(values):
                require(value == direct_hankel(n,coefficients),
                        f'moment/Christoffel {case_no,leading,n}')
                counts['direct_moment_determinant_equalities'] += 1

    # Distinct rational spectral parameters. Fit each sector separately and
    # verify both leading constants and values beyond the fitting range.
    patterns = [
        (0,0,[],3), (0,0,[(2,1)],2), (2,0,[(2,1)],2),
        (0,1,[(2,1)],2), (3,2,[],-2), (0,0,[(2,2)],4),
        (0,0,[(2,4)],16), (2,1,[(2,2),(3,1)],12),
        (1,0,[(2,2),(3,2)],36), (1,2,[(-2,2),(3,1)],12),
        (0,0,[(2,1),(3,1),(5,1)],30), (4,0,[(2,2)],4),
    ]
    sector_data = []
    example_rows = []
    for m,ell,blocks,leading in patterns:
        roots = ([Root(0,m)] if m else []) + ([Root(4,ell)] if ell else [])
        roots += [Root(2+F(z)+1/F(z),t) for z,t in blocks]
        ss = sectors(m,ell,blocks,leading)
        bound = sharp_order_bound(m,ell,[t for z,t in blocks])
        require(sum(s.degree+1 for s in ss) == bound, 'summed order formula')
        counts['order_sum_identities'] += 1
        values = christoffel_values(roots,leading,2*bound+6)
        require(determinant([[values[i+j] for j in range(bound)]
                             for i in range(bound)]) == secondary_hankel_formula(ss),
                'secondary Hankel factorization')
        counts['secondary_hankel_factorizations'] += 1
        polys = fit_sectors(values,ss)
        for s,p in zip(ss,polys):
            require(p[-1] == s.leading and p[-1] != 0, 'sector leading coefficient')
            counts['exact_sector_degree_and_leading_constant_checks'] += 1
        for n,value in enumerate(values):
            require(sum(peval(p,n)*s.rate**n for s,p in zip(ss,polys)) == value,
                    f'sector expansion {m,ell,blocks,n}')
            counts['exact_exponential_expansion_equalities'] += 1
        chi = characteristic(ss)
        for residual in recurrence_residuals(values,chi):
            require(residual == 0, 'nonresonant recurrence')
            counts['nonresonant_recurrence_residuals'] += 1
        if bound <= 15:
            require(minimal_recurrence(values,bound) == chi, 'sharp minimal order')
            counts['nonresonant_minimal_recurrence_recoveries'] += 1
        record = {'m':m, 'ell':ell, 'spectral_blocks':blocks,
                  'leading_coefficient':leading, 'order':bound,
                  'roots':encode_roots(roots),
                  'characteristic':list(map(str,chi)),
                  'sectors':[{'counts':s.counts,'rate':str(s.rate),
                              'degree':s.degree,'leading':str(s.leading),
                              'polynomial':list(map(str,p))}
                             for s,p in zip(ss,polys)]}
        sector_data.append(record)
        if (m,ell,blocks,leading) == (0,0,[(2,4)],16):
            example_rows = [(n,str(v)) for n,v in enumerate(values)]

    # Resonant rational root values: no complex arithmetic or root choices
    # are needed by the finite minimal-recurrence algorithm.
    resonant_data = []
    for c in (1,2,3):
        for t in range(1,5):
            roots = [Root(c,t)]
            bound = sharp_order_bound(0,0,[t])
            values = christoffel_values(roots,1,2*bound+8)
            chi = minimal_recurrence(values,bound)
            for residual in recurrence_residuals(values,chi):
                require(residual == 0, 'resonant recurrence residual')
                counts['resonant_recurrence_residuals'] += 1
            counts['resonant_minimal_recurrence_recoveries'] += 1
            resonant_data.append({'root':c,'multiplicity':t,'proved_bound':bound,
                                  'minimal_order':len(chi)-1,
                                  'characteristic':list(map(str,chi)),
                                  'initial_values':list(map(str,values))})

    # Inter-root resonance: different roots, multiplicatively dependent z_i.
    for blocks in ([(2,2),(4,1)],[(2,1),(-2,1)],[(2,1),(4,1),(8,1)]):
        roots = [Root(2+F(z)+1/F(z),t) for z,t in blocks]
        bound = sharp_order_bound(0,0,[t for z,t in blocks])
        ss = sectors(0,0,blocks)
        values = christoffel_values(roots,1,2*bound+8)
        chi = minimal_recurrence(values,bound)
        require(not any(recurrence_residuals(values,characteristic(ss,True))),
                'grouped annihilator')
        require(not any(recurrence_residuals(values,chi)), 'inter-root resonance')
        require(determinant([[values[i+j] for j in range(bound)]
                             for i in range(bound)]) == secondary_hankel_formula(ss),
                'resonant secondary Hankel factorization')
        counts['secondary_hankel_factorizations'] += 1
        counts['inter_root_resonance_recoveries'] += 1
        resonant_data.append({'spectral_blocks':blocks, 'roots':encode_roots(roots),
                              'proved_bound':bound,'minimal_order':len(chi)-1,
                              'characteristic':list(map(str,chi)),
                              'grouped_annihilator_order':len(characteristic(ss,True))-1})

    # Root-free multiplicity profiles and recurrences for irreducible factors.
    for roots in root_cases:
        m,ell,profile = multiplicity_profile(multiplier(roots))
        expected = Counter(r.multiplicity for r in roots if r.value not in (0,4))
        require(m == sum(r.multiplicity for r in roots if r.value == 0), 'profile at 0')
        require(ell == sum(r.multiplicity for r in roots if r.value == 4), 'profile at 4')
        require(profile == dict(expected), 'other-root profile')
        counts['root_free_multiplicity_profiles'] += 1
    rational_input_data = []
    for coefficients in ([1,0,1], [1,0,2,0,1], [-8,12,-6,1]):
        chi,bound = recurrence_from_coefficients(coefficients,max_bound=15)
        extra = [direct_hankel(n,coefficients) for n in range(2*bound+4)]
        require(not any(recurrence_residuals(extra,chi)), 'root-free recurrence')
        counts['root_free_recurrence_recoveries'] += 1
        rational_input_data.append({'coefficients':coefficients,'bound':bound,
                                    'profile':multiplicity_profile(coefficients),
                                    'characteristic':list(map(str,chi))})
    (args.out/'rational_input_examples.json').write_text(
        json.dumps(rational_input_data,indent=2)+'\n')

    # The nine-value certificate in the article proves the fourth-power
    # central-root formula once the all-index annihilator has been proved.
    centre_values = christoffel_values([Root(2,4)],1,40)
    centre_polynomial = [F(1)]
    for v in (1,2,2,3):
        centre_polynomial = pmul(centre_polynomial,[v,1])
    centre_polynomial = [v/12 for v in centre_polynomial]
    for n,value in enumerate(centre_values):
        require(value == peval(centre_polynomial,n), 'central-root product')
        counts['central_root_product_equalities'] += 1
    centre_certificate = {'multiplier':'(x-2)^4','annihilator':'(X-1)^5*(X+1)^4',
                          'values_required':9,
                          'values':list(map(str,centre_values[:9])),
                          'polynomial':list(map(str,centre_polynomial))}

    report = {'status':'PASS','arithmetic':'exact rational; Python standard library',
              'proof_status':'finite audit; universal arguments are in article.tex',
              'checks':dict(counts),'total_checks':sum(counts.values()),
              'direct_parameter_cases':len(root_cases)*2,
              'nonresonant_patterns':len(patterns)}
    for filename,obj in [('verification.json',report),('sectors.json',sector_data),
                         ('resonances.json',resonant_data),
                         ('central_root_certificate.json',centre_certificate)]:
        (args.out/filename).write_text(json.dumps(obj,indent=2)+'\n')
    with (args.out/'fourth_power_sequence.csv').open('w',newline='') as f:
        writer = csv.writer(f); writer.writerow(['N','H_N']); writer.writerows(example_rows)
    lines = ['PASS: exact verification suite',
             'Finite checks supplement, and do not replace, the all-parameter proofs.']
    lines += [f'{key}: {count}' for key,count in counts.items()]
    lines += [f'TOTAL: {sum(counts.values())}',
              f'Direct parameter cases: {len(root_cases)*2}',
              f'Nonresonant patterns: {len(patterns)}']
    text = '\n'.join(lines)+'\n'
    (args.out/'verification.txt').write_text(text)
    print(text,end='')


if __name__ == '__main__':
    main()
