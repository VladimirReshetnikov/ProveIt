#!/usr/bin/env python3
"""Emit the ordinary-strong blank constructions from package06 system61.

Only the standard library is needed. The source is a JSON arithmetic circuit,
not executable Python. This generator does not materialize compiler constants.

Example:
  python3 build_ordinary.py --base vendor/fixed_blank_system_61.json --out data
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ledger(source):
    return {'operations': len(source),
            'M': sum(r[1] == '*' for r in source),
            'A': sum(r[1] != '*' for r in source)}


def build(base):
    require(len(base['source']) == 61, 'expected package06 system61')
    require(base['fixed_numerals'] == ['Bm1', 'Kconstant', 'MC', 'MF'],
            'unexpected compiler ports')
    old = {r[0]: r for r in base['source']}
    expected = {
        'aux_coefficient_root': ['aux_coefficient_root', '*', 'i', 'Ac2'],
        'R16': ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
        'scaled_f_square': ['scaled_f_square', '*', 'A', 'L16'],
        'norm_strong': ['norm_strong', '-', 'scaled_f_square', 'R16'],
    }
    for name, row in expected.items():
        require(old.get(name) == row, 'unexpected strong block: ' + name)
    replacement = [
        ['f2_minus_one', '-', 'L16', 1],
        ['R16', '*', 'A', 'f2_minus_one'],
        ['ordinary_ic2', '*', 'i', 'c2'],
        ['ordinary_ic2_square', '*', 'ordinary_ic2', 'ordinary_ic2'],
    ]
    source = []
    for row in base['source']:
        if row[0] in expected:
            if row[0] == 'aux_coefficient_root':
                source.extend(replacement)
        else:
            source.append(deepcopy(row))
    comparisons = [(['ordinary_ic2_square', 'R16'] if a == 'norm_strong'
                    else [a, b]) for a, b in base['comparisons']]
    common = {k: deepcopy(base[k]) for k in
              ['fixed_numerals', 'witness_domain', 'witnesses']}
    system = dict(common, name='blank_ordinary_system61', source=source,
                  comparisons=comparisons, ledger=ledger(source),
                  residual_exact_degrees=[22, 18, 28, 7, 2, 22],
                  proof='ordinary_strong.md')
    psource = deepcopy(source)
    psource.extend([
        ['ordinary_unit_partial', '+', 'ordinary_ic2_square', 1],
        ['norm_ordinary', '-', 'ordinary_unit_partial', 'R16'],
    ])
    factors = [a for a, _ in comparisons[:5]] + ['norm_ordinary']
    last = factors[0]
    for i, factor in enumerate(factors[1:]):
        name = 'product_' + str(i)
        psource.append([name, '*', last, factor])
        last = name
    psource.append(['polynomial', '-', last, 1])
    product = dict(common, name='blank_ordinary_poly69', source=psource,
                   output='polynomial', factors=factors,
                   ledger=ledger(psource),
                   factor_exact_degrees=[22, 18, 28, 7, 2, 22], exact_degree=99)
    ssource = deepcopy(source)
    for i, (a, b) in enumerate(comparisons):
        ssource.extend([[f'residual_{i}', '-', a, b],
                        [f'square_{i}', '*', f'residual_{i}', f'residual_{i}']])
    last = 'square_0'
    for i in range(1, len(comparisons)):
        name = 'sum_' + str(i)
        ssource.append([name, '+', last, 'square_' + str(i)])
        last = name
    sos = dict(common, name='blank_ordinary_sos78', source=ssource,
               output=last, ledger=ledger(ssource), exact_degree=56)
    return system, product, sos


def quadratic(common):
    registers = ['N', 'E', 'P', 'c', 'a', 'X', 'D', 'C2', 'G', 'L', 'R',
                 'F2', 'V0', 'V', 'g', 'I', 'Baux', 'Delta']
    equations = [
        'L = (Bm1*Jrep + 1)**2 - 1',
        'N = (L + 1)*(Bm1*Jrep + 1)',
        'X = w*(Bm1*Jrep + 1)',
        'a = E + N*s',
        'E = X*(-E + a)',
        'c = eta + (-E + a)*(eta + zeta)',
        'P = E*(c - eta) + eta + zeta',
        'tau_root**2 = P*(P - eta - zeta) + 1',
        'D = X + a*c + gamma*(4*a + 3)',
        'D**2 = Delta*C2 + 1',
        'Delta = a**2 + 4*a + 3',
        'C2 = c**2',
        'eta + zeta = E*h + R + 1',
        'G = Bm1*Jrep*(Bm1*Jrep - F + 1) + alpha',
        'R = G*L + Jrep*(MC + MF*(Bm1*Jrep + 1))',
        '-Bm1*Jrep*transport_quotient + Bm1*Jrep - F + '
        '(Kconstant + w)*(Bm1*Jrep - F - alpha + 1) + 1 = 1',
        'F2 = f**2',
        'V0 = auxiliary_quotient*f - 1',
        'V = -F2*R + V0*c',
        'g = -V**2 + y_aux**2',
        'I = i*C2',
        'Baux = I**2',
        'Baux = Delta*(F2 - 1)',
        '-Baux*g + y_aux**2 = 1',
    ]
    residuals = [
        '-Bm1**2*Jrep**2 - 2*Bm1*Jrep + L',
        '-Bm1*Jrep*L - Bm1*Jrep - L + N - 1',
        '-Bm1*Jrep*w + X - w',
        '-E - N*s + a',
        'E*X + E - X*a',
        'E*eta + E*zeta - a*eta - a*zeta + c - eta',
        '-E*c + E*eta + P - eta - zeta',
        '-P**2 + P*eta + P*zeta + tau_root**2 - 1',
        'D - X - a*c - 4*a*gamma - 3*gamma',
        'D**2 - Delta*C2 - 1',
        'Delta - a**2 - 4*a - 3',
        'C2 - c**2',
        '-E*h - R + eta + zeta - 1',
        '-Bm1**2*Jrep**2 + Bm1*F*Jrep - Bm1*Jrep + G - alpha',
        '-Bm1*Jrep**2*MF - G*L - Jrep*MC - Jrep*MF + R',
        'Bm1*Jrep*Kconstant - Bm1*Jrep*transport_quotient + Bm1*Jrep*w + '
        'Bm1*Jrep - F*Kconstant - F*w - F - Kconstant*alpha + Kconstant - '
        'alpha*w + w',
        'F2 - f**2',
        'V0 - auxiliary_quotient*f + 1',
        'F2*R + V - V0*c',
        'V**2 + g - y_aux**2',
        'I - i*C2',
        'Baux - I**2',
        'Baux - Delta*F2 + Delta',
        '-Baux*g + y_aux**2 - 1',
    ]
    return {
        'description': '24 quadratic equations in 33 strictly positive '
                       'unknowns, for ordinary strong-root blank system.',
        'fixed_numerals': common['fixed_numerals'],
        'original_witnesses': common['witnesses'],
        'register_witnesses': registers,
        'variables': common['witnesses'] + registers,
        'variable_count': 33, 'equation_count': 24,
        'linear_abbreviations': {'q': 'Bm1*Jrep+1', 'k': 'eta+zeta',
                                 'H': '4*a+3'},
        'equations_factored': equations,
        'residual_polynomials': residuals,
        'max_equation_degree': 2, 'sum_of_squares_exact_degree': 4,
        'nonnegative_version': 'Replace each of 33 positive unknowns v by n_v+1.',
        'claim_scope': 'Equivalent to ordinary strong-root blank system61 '
                       'by the explicitly proved positive register lift; '
                       'same fixed coefficient recipe as raw-K215 blank67, '
                       'not the distinct Start-only coefficients.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, required=True,
                        help='package06/data/fixed_blank_system_61.json')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    data = args.base.read_bytes()
    system, product, sos = build(json.loads(data))
    q = quadratic(system)
    args.out.mkdir(parents=True, exist_ok=True)
    packets = {'blank_ordinary_system61.json': system,
               'blank_ordinary_poly69.json': product,
               'blank_ordinary_sos78.json': sos,
               'blank_ordinary_quartic33.json': q}
    for name, packet in packets.items():
        (args.out / name).write_text(json.dumps(packet, indent=2) + '\n')
    receipt = {'source_sha256': hashlib.sha256(data).hexdigest(),
               'emitted': {name: hashlib.sha256((args.out / name).read_bytes()).hexdigest()
                           for name in packets},
               'scope': 'Exact circuit transformation and explicit quadratic equations; '
                        'valid raw-K215 coefficient recipe and mathematical bridge '
                        'are separate proof dependencies.'}
    (args.out / 'build_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
