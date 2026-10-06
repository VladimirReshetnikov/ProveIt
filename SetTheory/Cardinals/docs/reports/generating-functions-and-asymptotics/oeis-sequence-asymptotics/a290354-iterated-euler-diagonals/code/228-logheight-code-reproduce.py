#!/usr/bin/env python3
"""Reproduce Report228's exact finite algebra and unvalidated finite-n table.

Python 3.11+, mpmath 1.3.0, SymPy 1.14.0 were used for the distributed run.
The source code never modifies sys.set_int_max_str_digits or global precision.
"""
import argparse
from decimal import Decimal, ROUND_FLOOR, localcontext
from fractions import Fraction
from hashlib import sha256
import json
import os
from math import factorial
from pathlib import Path
import sys

from exact_euler import (MAX_INDEX, bounded_index, coefficients, decimal_integer,
                        euler_step, euler_zigzag, exact_targets, product_step)
from finite_algebra import (KNOWN_COORDINATE, coordinate_coefficients,
                            endpoint_coefficients, inverse_identity_check,
                            rational_string)

DEGREES = (20, 40, 80)
LAMBDAS = ('0.5', '1', '1.5')
DECIMAL_PRECISION = 80
NUMERIC_PRECISION = 80
SOURCE_DIR = Path(__file__).resolve().parent
PACKAGE_DIR = SOURCE_DIR.parent
OUTPUT_FILENAMES = ('reproduction.json', 'crossover_table.tex', 'checks.json')


def equal(actual, expected, label):
    if actual != expected:
        raise ArithmeticError('check failed: '+label)


def rejects(function, label):
    try:
        function()
    except ValueError:
        return
    raise ArithmeticError('guard did not reject: '+label)


def floor_height(n, lambda_string, precision=DECIMAL_PRECISION):
    """Decimal evaluation of floor(lambda*n*log(n)); not an interval proof."""
    bounded_index(n)
    if n < 2 or lambda_string not in LAMBDAS:
        raise ValueError('floor diagnostics support n>=2 and lambda in {0.5,1,1.5}')
    if isinstance(precision, bool) or not isinstance(precision, int) or not 40 <= precision <= 320:
        raise ValueError('Decimal precision must be an integer from 40 to 320')
    with localcontext() as context:
        context.prec = precision
        raw = Decimal(lambda_string)*n*Decimal(n).ln()
        height = int(raw.to_integral_value(rounding=ROUND_FLOOR))
        distance = min(raw-height, height+1-raw)
    bounded_index(height)
    return height, str(raw), str(distance)


def finite_table():
    import mpmath
    # A private context avoids changing mp.mp.dps for an importing application.
    mp = mpmath.mp.clone()
    mp.dps = NUMERIC_PRECISION
    T = mp.pi/2
    B = mp.mpf(1)/2-mp.pi/6-mp.pi**2/16-mp.log(2)/6
    K = (1-mp.euler+mp.log(T/2))/3-B
    c2 = (9-mp.pi**2)/108
    c3 = mp.mpf(17)/1080-mp.zeta(3)/81
    render = lambda value: mp.nstr(value, 30, strip_zeros=False)
    rows = []
    for n in DEGREES:
        requested = [floor_height(n, lam) for lam in LAMBDAS]
        counts = exact_targets(n, [item[0] for item in requested])
        zigzag = euler_zigzag(n-1)
        ell = Fraction(zigzag, factorial(n-1))
        for lam, (m, floor_input, distance) in zip(LAMBDAS, requested):
            m_check, _, _ = floor_height(n, lam, 2*DECIMAL_PRECISION)
            equal(m_check, m, '80/160-digit floor agreement')
            beta = mp.mpf(n)/m
            L = mp.log(n)
            lm = mp.mpf(lam)
            # Passing the integer directly avoids any decimal-string conversion.
            log_R = mp.log(mp.mpf(counts[m]))-mp.log(2)+n*mp.log(T)-(n-1)*mp.log(m)
            leading = mp.exp(-1/(3*lm))
            order2 = leading*(1+K/(lm*L)+(K*K/2+c2)/(lm*L)**2)
            floor_adjusted = mp.exp(-beta*L/3)*(1+K*beta+(K*K/2+c2)*beta**2)
            ell_mp = mp.mpf(ell.numerator)/mp.mpf(ell.denominator)
            log_Kaneiwa = mp.log(mp.mpf(counts[m]))-mp.log(ell_mp)-(n-1)*mp.log(m-1)
            order2_Kaneiwa = leading*(1+(K+1)/(lm*L)+((K+1)**2/2+c2)/(lm*L)**2)
            rows.append({
                'n': n, 'lambda': lam, 'm': m,
                'A_nm_decimal': decimal_integer(counts[m]),
                'A_nm_digit_count': len(decimal_integer(counts[m])),
                'height_floor_input_decimal': floor_input,
                'height_distance_to_nearest_integer_decimal': distance,
                'height_floor_agrees_at_80_and_160_digits': True,
                'beta': render(beta),
                'ratio_R': render(mp.exp(log_R)),
                'leading_limit': render(leading),
                'order2_ratio_lambda': render(order2),
                'order2_ratio_exact_beta': render(floor_adjusted),
                'log_R': render(log_R),
                'log_R_minus_order2_log_model': render(log_R+beta*L/3-K*beta-c2*beta**2),
                'kaneiwa_ell_n_exact_rational': rational_string(ell),
                'kaneiwa_ratio': render(mp.exp(log_Kaneiwa)),
                'kaneiwa_order2_ratio_lambda': render(order2_Kaneiwa),
                'kaneiwa_log_shift_minus_beta': render(log_Kaneiwa-log_R-beta),
            })
    return {
        'status': 'A(n,m) and ell_n are exact; all logarithms, floors, constants, normalized ratios and approximations are unvalidated numerical computations',
        'precision': {'Decimal_floor_digits': DECIMAL_PRECISION,
                      'Decimal_floor_crosscheck_digits': 2*DECIMAL_PRECISION,
                      'mpmath_working_decimal_digits': NUMERIC_PRECISION,
                      'display_significant_digits': 30},
        'normalization': 'R(n,m)=A(n,m)/(2*T**(-n)*m**(n-1)); T=pi/2',
        'height_rule': 'm=floor(lambda*n*log(n)); natural logarithm; Decimal floor agreement is not an interval certificate',
        'order2_ratio_lambda_formula': 'exp(-1/(3*lambda))*(1+K/(lambda*log(n))+(K**2/2+c2)/(lambda*log(n))**2)',
        'order2_ratio_exact_beta_formula': 'exp(-beta*log(n)/3)*(1+K*beta+(K**2/2+c2)*beta**2), beta=n/m',
        'kaneiwa_normalization': 'A(n,m)/(ell_n*(m-1)**(n-1)), ell_n=E_(n-1)/(n-1)!; use K+1 for its higher corrections',
        'constants': {'T': render(T), 'B': render(B), 'K': render(K), 'c2': render(c2), 'c3': render(c3)},
        'rows': rows,
    }


def self_checks():
    original_limit = sys.get_int_max_str_digits()
    checked = 0
    def check(actual, expected, label):
        nonlocal checked
        equal(actual, expected, label)
        checked += 1
    def reject(function, label):
        nonlocal checked
        rejects(function, label)
        checked += 1
    check(coefficients(5, 0), [0,1,0,0,0,0], 'F0')
    check(coefficients(5, 1), [0,1,1,1,1,1], 'F1')
    check(coefficients(5, 2), [0,1,2,3,5,7], 'F2 partition coefficients')
    check(exact_targets(3, [0,1,2,3]), {0:0,1:1,2:3,3:6}, 'small A(3,m)')
    check(exact_targets(0, [0,640]), {0:1,640:1}, 'array constant convention and maximum height')
    check(len(coefficients(640,0)), 641, 'maximum degree accepted')
    check(coefficients(0,640), [0], 'F constant zero at maximum height')
    row = [0,1]+[0]*11
    product = row[:]
    for h in range(1,13):
        row = euler_step(row)
        product = product_step(product)
        check(row, product, 'independent product, degree 12, height '+str(h))
    degree20_targets = exact_targets(20, [29,59,89])
    product20 = [0,1]+[0]*19
    for h in range(1,90):
        product20 = product_step(product20)
        if h in degree20_targets:
            check(product20[20], degree20_targets[h], 'degree-20 table count by independent product')
    check([euler_zigzag(j) for j in range(10)], [1,1,1,2,5,16,61,272,1385,7936], 'Euler zigzag initial coefficients')
    for order in range(13):
        values = coordinate_coefficients(order)
        check(len(values), order, 'coordinate length')
        check(values[:9], KNOWN_COORDINATE[:min(order,9)], 'coordinate exact coefficients')
    for order in range(2,8):
        endpoint_coefficients(order)
        checked += 1
    inverse = inverse_identity_check()
    checked += 3
    for bad in (-1,641,True,1.5,'5',None):
        reject(lambda bad=bad: bounded_index(bad), 'index/height')
        reject(lambda bad=bad: coefficients(bad,0), 'degree')
        reject(lambda bad=bad: coefficients(0,bad), 'height')
        reject(lambda bad=bad: exact_targets(1,[bad]), 'target height')
    for bad in ([],[1],[0,-1],[0,True],[0,1.5],(0,1),None,[0]*642):
        reject(lambda bad=bad: euler_step(bad), 'row')
    for bad in ([],None,{},[641],[True]):
        reject(lambda bad=bad: exact_targets(1,bad), 'target list')
    for bad in (-1,13,True,1.5,'7',None):
        reject(lambda bad=bad: coordinate_coefficients(bad), 'coordinate order')
    for bad in (0,1,8,True,1.5,'7',None):
        reject(lambda bad=bad: endpoint_coefficients(bad), 'endpoint order')
    reject(lambda: product_step([0]*22), 'independent product degree cap')
    for bad in (True,1.5,'1',None):
        reject(lambda bad=bad: decimal_integer(bad), 'integer serialization input')
    check(decimal_integer(0), '0', 'zero serialization')
    check(decimal_integer(10**3000), '1'+'0'*3000, 'positive 3001-digit serialization')
    check(decimal_integer(-10**3000), '-1'+'0'*3000, 'negative 3001-digit serialization')
    check(json.loads(json.dumps({'integer':decimal_integer(10**3000)}))['integer'],
          '1'+'0'*3000, '3001-digit exact integer JSON round trip as a string')
    check(rational_string(Fraction(10**3000,3)), ('1'+'0'*3000)+'/3', 'large rational safe serialization')
    expected_heights = ((29,59,89), (73,147,221), (175,350,525))
    for n, heights in zip(DEGREES, expected_heights):
        check(tuple(floor_height(n, lam)[0] for lam in LAMBDAS), heights, 'table heights')
    for bad in (39,321,True,1.5,'80',None):
        reject(lambda bad=bad: floor_height(20,'1',bad), 'floor precision')
    reject(lambda: floor_height(1,'1'), 'floor degree')
    reject(lambda: floor_height(20,'2'), 'floor lambda')
    reject(lambda: floor_height(640,'1.5'), 'computed height cap')
    reject(lambda: validate_output_directory(SOURCE_DIR), 'output equals source directory')
    reject(lambda: validate_output_directory(SOURCE_DIR/'generated'), 'output inside source directory')
    reject(lambda: validate_output_directory(SOURCE_DIR.parent), 'output equals package')
    reject(lambda: validate_output_directory(PACKAGE_DIR/'results'), 'output inside package')
    reject(lambda: validate_output_directory(PACKAGE_DIR.parent), 'output ancestor of package')
    check(sys.get_int_max_str_digits(), original_limit, 'global integer digit limit unchanged')
    return {'status':'passed', 'explicit_checks':checked,
            'integer_string_limit':original_limit, 'python_optimization':sys.flags.optimize,
            'checks_use_assert':False,
            'finite_scope':'exact algebra and finite implementation checks only; no analytic or decimal certification'}, inverse


def latex_table(table):
    # Decimal parsing keeps the table deterministic and independent of float repr.
    def fixed(value):
        with localcontext() as context:
            context.prec = 50
            return format(Decimal(value), '.8f')
    lines = [
        '% Generated by code/reproduce.py; exact counts, unvalidated decimal diagnostics.',
        '% R2 is the explicit lambda-based second-order ratio expansion, not exp of a truncated logarithm.',
        r'\begin{tabular}{rrrrrr}',
        r'\hline',
        r'$n$ & $\lambda$ & $m$ & $R(n,m)$ & $e^{-1/(3\lambda)}$ & $R_2(n,\lambda)$ \\',
        r'\hline',
    ]
    for row in table['rows']:
        lines.append(f"{row['n']} & {row['lambda']} & {row['m']} & {fixed(row['ratio_R'])} & {fixed(row['leading_limit'])} & {fixed(row['order2_ratio_lambda'])} \\\\")
    lines += [r'\hline', r'\end{tabular}', '']
    return '\n'.join(lines)


def validate_output_directory(directory):
    directory = Path(os.path.abspath(directory.expanduser()))
    if any(p.is_symlink() for p in [directory, *directory.parents]):
        raise ValueError('output directory must have no symlink ancestor')
    # Keep every distributed package file unchanged, not only Python sources.
    if directory == PACKAGE_DIR or PACKAGE_DIR in directory.parents or directory in PACKAGE_DIR.parents:
        raise ValueError('output directory must not overlap the source package')
    if directory.exists() and not directory.is_dir():
        raise ValueError('output path is not a directory')
    for name in OUTPUT_FILENAMES:
        target = directory/name
        if target.is_symlink():
            raise ValueError('refusing to overwrite an output symlink: '+name)
        if target.exists() and not target.is_file():
            raise ValueError('output target is not a regular file: '+name)
    return directory


def write_text_atomic(path, content):
    temporary = path.with_name(path.name+'.tmp')
    if temporary.exists() or temporary.is_symlink():
        raise ValueError('temporary output already exists: '+str(temporary))
    try:
        with temporary.open('x', encoding='utf-8', newline='\n') as stream:
            stream.write(content)
        temporary.replace(path)
    finally:
        if temporary.exists():
            temporary.unlink()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--check', action='store_true', help='run optimization-safe checks before writing all outputs')
    args = parser.parse_args()
    try:
        output = validate_output_directory(args.output_dir)
        original_limit = sys.get_int_max_str_digits()
        checks, inverse = self_checks() if args.check else ({'status':'not requested; use --check'}, inverse_identity_check())
        endpoint = endpoint_coefficients(7)
        table = finite_table()
        equal(sys.get_int_max_str_digits(), original_limit, 'whole-run global integer digit limit unchanged')
        result = {
            'report':'Report228',
            'scope':'finite exact recurrence and algebra with unvalidated asymptotic illustrations; no effective onset or certified numerical error bounds',
            'caps':{'maximum_degree':MAX_INDEX,'maximum_height':MAX_INDEX,'maximum_coordinate_order':12,'maximum_endpoint_order':7},
            'endpoint':endpoint, 'inverse':inverse, 'finite_table':table,
        }
        encoded = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True)+'\n'
        output.mkdir(parents=True, exist_ok=True)
        write_text_atomic(output/'reproduction.json', encoded)
        write_text_atomic(output/'crossover_table.tex', latex_table(table))
        write_text_atomic(output/'checks.json', json.dumps(checks, indent=2, sort_keys=True)+'\n')
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps({'status':'written', 'output_directory':str(output),
        'files':list(OUTPUT_FILENAMES), 'reproduction_sha256':sha256(encoded.encode()).hexdigest(),
        'self_checks':checks['status']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
