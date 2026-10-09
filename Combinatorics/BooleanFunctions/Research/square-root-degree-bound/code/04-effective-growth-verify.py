#!/usr/bin/env python3
"""Exact certificates for Effective Power-Law Fourier Growth.

Python 3.10+; standard library only. No floating-point calculations or
external theorem prover are used. Run from any directory:
  python code/verify.py --output certificates/verification.json
The default search covers every distinct-singleton binomial reporting rule
with block width 1 <= r <= 4 and 2 <= m <= r+1. This is a restricted family,
not an exhaustive search over all low-degree observations.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import comb, factorial, prod
from pathlib import Path


def require(test: bool, message: str) -> None:
    if not test:
        raise AssertionError(message)


def label(state: tuple[int, ...], centers: tuple[int, ...],
          selector: dict[int, int]) -> tuple:
    """Exact tagged reporting rule. Selector indices are zero-based."""
    u, *z = state
    i = selector[u]
    passes = [z[j] == centers[j] for j in range(len(z))]
    if all(passes):
        return ('B', *z)
    if all(passes[j] for j in range(len(z)) if j != i):
        return ('A',)
    return ('C', u, i, *(z[j] for j in range(len(z)) if j != i))


def tensor_transform(values: dict[tuple[int, ...], int], r: int,
                     blocks: int) -> dict[tuple[int, ...], int]:
    """Integer Fourier numerators for functions symmetric within each block.

    Input keys are plus-counts. Output keys are subset sizes in each block.
    For any one fixed subset with those sizes the coefficient is numerator
    divided by 2**(r*blocks); binomial multiplicities are NOT included.
    """
    M = [[sum((-1)**(k-t) * comb(k, t) * comb(r-k, j-t)
              for t in range(k+1) if 0 <= j-t <= r-k)
          for j in range(r+1)] for k in range(r+1)]
    data = values.copy()
    for axis in range(blocks):
        out = {}
        for key in product(range(r+1), repeat=blocks):
            out[key] = sum(M[key[axis]][j] *
                          data[key[:axis] + (j,) + key[axis+1:]]
                          for j in range(r+1))
        data = out
    return data


def twenty_bit_certificate() -> dict:
    r, m, blocks = 4, 4, 5
    centers = (-4, -2, 0, 2)
    support = tuple(range(-r, r+1, 2))
    selector = dict(zip(support, (1, 0, 1, 2, 3)))
    cells: dict[tuple, list[int]] = {}
    states = []
    for plus in product(range(r+1), repeat=blocks):
        state = tuple(2*j-r for j in plus)
        weight = prod(comb(r, j) for j in plus)
        L = sum(state)
        lab = label(state, centers, selector)
        acc = cells.setdefault(lab, [0, 0, 0])
        acc[0] += weight
        acc[1] += weight*L
        acc[2] += weight*L*L
        states.append((plus, state, weight, lab))
    total = 2**(r*blocks)
    require(sum(v[0] for v in cells.values()) == total, 'total mass')
    require(sum(v[1] for v in cells.values()) == 0, 'centered sum')
    require(sum(v[2] for v in cells.values()) == total*r*blocks, 'sum variance')
    variance = sum(F(s*s, n*total) for n, s, _ in cells.values())
    fourth = sum(F(s**4, n**3*total) for n, s, _ in cells.values())
    correlation = sum(F(abs(s), total) for _, s, _ in cells.values())
    mean_readout = sum(F(n * (1 if s >= 0 else -1), total)
                       for n, s, _ in cells.values())
    an, as_, ass = cells[('A',)]
    amean = F(as_, an)
    avar = F(ass, an)-amean**2
    require(len(cells) == 622, 'cell count')
    require(variance == 16 + F(9, 34816), 'retained variance')
    require(F(an, total) == F(17, 2048), 'exceptional probability')
    require(amean == -F(31, 17), 'exceptional mean')
    require(avar == F(1147, 289), 'exceptional variance')
    require(correlation < 4, 'sign readout is not a Boolean violation')

    avalues, fvalues = {}, {}
    for plus, state, _, lab in states:
        avalues[plus] = int(lab == ('A',))
        fvalues[plus] = 1 if cells[lab][1] >= 0 else -1
        u, *z = state
        lhs = int(lab == ('A',))
        rhs = sum(int(selector[u] == i) *
                  prod(int(z[j] == centers[j]) for j in range(m) if j != i)
                  for i in range(m)) - prod(int(z[j] == centers[j]) for j in range(m))
        require(lhs == rhs, 'pointwise cancellation')
    a_fourier = tensor_transform(avalues, r, blocks)
    f_fourier = tensor_transform(fvalues, r, blocks)
    a_degree = max(sum(k) for k, v in a_fourier.items() if v)
    f_degree = max(sum(k) for k, v in f_fourier.items() if v)
    require(a_degree == 16, 'exceptional-cell degree')
    require(f_degree <= 16, 'sign-readout degree')
    singleton_sum = sum(F(r*f_fourier[tuple(int(j == i) for j in range(blocks))], total)
                        for i in range(blocks))
    require(singleton_sum == correlation, 'independent Fourier correlation')
    # Independently certify one ordinary cell attaining degree 16.
    ordinary_label = next(lab for lab in cells if lab[0] == 'C')
    ovalues = {plus: int(lab == ordinary_label) for plus, _, _, lab in states}
    o_fourier = tensor_transform(ovalues, r, blocks)
    o_degree = max(sum(k) for k, v in o_fourier.items() if v)
    require(o_degree == 16, 'ordinary-cell degree')
    return {
        'bits': 20, 'block_sum_states': len(states), 'output_cells': len(cells),
        'centers': centers, 'selector_one_based': [selector[u]+1 for u in support],
        'total_bit_strings': total, 'exceptional_bit_strings': an,
        'exceptional_probability': str(F(an, total)),
        'exceptional_mean': str(amean), 'exceptional_variance': str(avar),
        'retained_variance': str(variance), 'variance_gain': str(variance-16),
        'standardized_fourth_moment': str(fourth/variance**2),
        'sign_readout_singleton_sum': str(correlation),
        'sign_readout_mean': str(mean_readout), 'sign_readout_degree': f_degree,
        'exceptional_cell_degree': a_degree, 'ordinary_cell_degree': o_degree,
        'special_cell_fourier_above_16_all_zero': True,
        'pointwise_cancellation_states_checked': len(states),
        'max_degree_special_coefficient_example': next(
            {'block_degrees': k, 'coefficient': str(F(v, total))}
            for k, v in a_fourier.items() if v and sum(k) == 16),
    }


def exhaustive_singleton_search(r: int, m: int) -> dict:
    """Exact exhaustive search; common denominators avoid Fraction inner loops."""
    support = tuple(range(-r, r+1, 2))
    weights = [comb(r, j) for j in range(r+1)]
    mass = 2**r
    best: F | None = None
    best_data = None
    checked = positive = 0
    for indices in combinations(range(r+1), m):
        centers = tuple(support[i] for i in indices)
        beta_weights = [weights[i] for i in indices]
        denom = prod(beta_weights)  # divisible by every beta weight
        ratios = [[weights[x]*denom//beta_weights[i] for i in range(m)]
                  for x in range(r+1)]
        diffs = [[support[x]-centers[i] for i in range(m)] for x in range(r+1)]
        for selector in product(range(m), repeat=r+1):
            checked += 1
            kn = sum(ratios[x][i] for x, i in enumerate(selector))-denom
            if kn == 0:  # A is empty: retained variance equals the baseline.
                gain = F(0)
                bn = qn = 0
            else:
                bn = sum(ratios[x][i]*diffs[x][i] for x, i in enumerate(selector))
                qn = sum(ratios[x][i]*diffs[x][i]**2 for x, i in enumerate(selector))
                # p_* = denom/mass**m; B1=bn/denom; Q=qn/denom; K=kn/denom.
                gain = F(bn*bn-qn*kn, kn*mass**m)
            if gain > 0:
                positive += 1
            if best is None or gain > best:
                best = gain
                best_data = {'centers': centers, 'selector_one_based': [i+1 for i in selector],
                             'K': str(F(kn, denom)), 'B1': str(F(bn, denom)),
                             'Q': str(F(qn, denom))}
    require(checked == comb(r+1, m)*m**(r+1), 'search coverage')
    require(best is not None, 'nonempty search')
    return {'block_width': r, 'leaves': m, 'cell_degree_bound': r*m,
            'rules_checked': checked, 'positive_rules': positive,
            'maximum_variance_gain': str(best), 'maximizer': best_data}


def elementary_constants() -> dict:
    """Check finite rational inequalities used in the analytic certificate.

    Does not instantiate the astronomical batch ell or the Gaussian grid.
    The inequalities involving exp are justified by exact Taylor bounds.
    """
    m = 2**64 + 1
    # e < 11/4: sum 0..5 plus geometrically bounded tail.
    e_upper = sum((F(1, factorial(k)) for k in range(6)), F(0)) + F(7, 6*factorial(6))
    e3_lower = sum((F(3**k, factorial(k)) for k in range(7)), F(0))
    checks = {
        'e_upper_below_11_over_4': e_upper < F(11, 4),
        'e_cubed_lower_above_16': e3_lower > 16,
        'e14_upper_below_2pow21': F(11, 4)**14 < 2**21,
        'e_upper_below_sqrt8': F(11, 4)**2 < 8,
        'tail_bound_below_1_over_16': F(53, 2**15) < F(1, 16),
        'central_numerator_below_2pow_minus120': 198 < 256,
        'gaussian_radius_square_below_99': (F(14)+F(1,16))**2 / 2 < 99,
        'm_h_squared_below_1_over_16': F(m, 2**192) < F(1, 16),
        'shift_error_below_grid_allowance': F(m+14, 2**192) < F(1,2**64),
        'transfer_exponent_check': 9 + 3*65 <= 252*m,
        'epsilon_exponent_below_2pow74': 260*m + 17 + 2*65 < 2**74,
        'central_density_log_error_below_half':
            14*F(13,2**64) + F(13,2**64)**2/2 + 14*F(1,2**96) + F(1,2**192)/2 < F(1,2),
    }
    for name, value in checks.items():
        require(value, name)
    return {'m': str(m), 'h': '2^(-96)', 'R': 13, 'b': str(m-1),
            'eta': '2^(-260*m-2)', 'batch_ell': '2^(4096*m)',
            'e_upper_rational': str(e_upper), 'e3_lower_rational': str(e3_lower),
            'checks': checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification.json'))
    args = parser.parse_args()
    witness = twenty_bit_certificate()
    search = [exhaustive_singleton_search(r, m)
              for r in range(1, 5) for m in range(2, r+2)]
    require(all(F(row['maximum_variance_gain']) <= 0 for row in search
                if row['block_width'] <= 3), 'no narrower singleton witness')
    require(next(F(row['maximum_variance_gain']) for row in search
                 if (row['block_width'], row['leaves']) == (4, 4)) == F(9,34816), 'search optimum')
    result = {'status': 'all exact checks passed', 'arithmetic': 'integers and rational numbers',
              'twenty_bit_witness': witness, 'restricted_exhaustive_search': search,
              'elementary_constant_checks': elementary_constants(),
              'scope': 'Finite identities and rational constants only; analytic theorems are proved in article.tex, not formally verified.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
