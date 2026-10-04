#!/usr/bin/env python3
"""Exact finite checks and diagnostics for the renewal theorem.

The all-index assertion is proved in the article.  This program checks
independent coefficient constructions and the exact large-part identity.
Only Python's standard library is required.
"""
import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def coefficients(count):
    """Triangular iterate hierarchy, on the finite domain n+k<=count+1."""
    rows = [[1] * (count + 2)]
    values = [1]
    for n in range(1, count + 1):
        row = [0] * (count + 2 - n)
        running = 0
        for k in range(1, len(row)):
            running += sum(rows[i][k] * rows[n-1-i][k+1]
                           for i in range(n))
            row[k] = running
        rows.append(row)
        values.append(row[1])
    return values


def multiply(left, right, degree):
    out = [0] * (degree + 1)
    for i, x in enumerate(left[:degree+1]):
        for j, y in enumerate(right[:degree+1-i]):
            out[i+j] += x * y
    return out


def direct_coefficients(count):
    """Independent extraction from A=1+sum a_k z^(k+1) A^(k+2)."""
    a = [1]
    for n in range(1, count + 1):
        power = multiply(a, a, n-1)
        value = 0
        for k in range(n):
            value += a[k] * power[n-1-k]
            power = multiply(power, a, n-1)
        a.append(value)
    return a


def renewal(a):
    c = [1]
    for n in range(1, len(a)):
        c.append(sum(a[j-1] * c[n-j] for j in range(1, n+1)))
    return c


def composition_weights(a, n):
    """Enumerate cut masks independently of the renewal recurrence."""
    total = giant = 0
    for cuts in range(1 << (n-1)):
        parts = []
        previous = 0
        for i in range(1, n):
            if cuts & (1 << (i-1)):
                parts.append(i-previous)
                previous = i
        parts.append(n-previous)
        weight = 1
        for size in parts:
            weight *= a[size-1]
        total += weight
        if 2 * max(parts) > n:
            giant += weight
    return total, giant


def decimal_fraction(value, digits=24):
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def verify(count=260):
    require(count >= 30, 'count must be at least 30')
    a = coefficients(count)
    independent = direct_coefficients(25)
    require(a[:26] == independent, 'independent formal equations disagree')
    published_a = [1, 1, 3, 13, 69, 419, 2809, 20353, 157199,
                   1281993, 10963825, 97828031, 907177801]
    require(a[:len(published_a)] == published_a, 'A088714 prefix mismatch')
    c = renewal(a)
    published_c = [1, 1, 2, 6, 24, 118, 674, 4308, 30062,
                   225266, 1791964, 15009118, 131566314]
    require(c[:len(published_c)] == published_c, 'A088713 prefix mismatch')
    d = [sum(c[i] * c[j-i] for i in range(j+1))
         for j in range(count+1)]
    require(d[:7] == [1, 2, 5, 16, 64, 308, 1716], 'C squared mismatch')
    cases = 0
    for n in range(1, 15):
        total, giant = composition_weights(a, n)
        exact_giant = sum(a[n-j-1] * d[j] for j in range((n+1)//2))
        require(total == c[n], f'composition total mismatch at {n}')
        require(giant == exact_giant, f'large-part identity mismatch at {n}')
        cases += 1 << (n-1)
    indices = sorted({20, 30, 50, 100, 200, count} & set(range(count+1)))
    diagnostics = []
    for n in indices:
        row = {'n': n, 'companion_over_previous': decimal_fraction(Fraction(c[n], a[n-1]))}
        for k in range(4):
            residual = c[n] - sum(d[j] * a[n-1-j] for j in range(k+1))
            require(residual >= 0, f'negative exact residual at {n}, K={k}')
            row[f'residual_K{k}_over_next_shift'] = decimal_fraction(Fraction(residual, a[n-k-2]))
        diagnostics.append(row)
    return {
        'status': 'PASS',
        'coefficient_max_n': count,
        'independent_formal_coefficients': 26,
        'explicit_compositions_checked': cases,
        'giant_identity_sizes': list(range(1, 15)),
        'd_coefficients': d[:10],
        'diagnostics': diagnostics,
        'scope': 'Exact finite identities; finite diagnostics do not prove asymptotics.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--count', type=int, default=260)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'data' / 'renewal_checks.json')
    args = parser.parse_args()
    report = verify(args.count)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('PASS: independent formal coefficients, OEIS prefixes, and '
          f"{report['explicit_compositions_checked']} exact compositions.")
    for row in report['diagnostics']:
        print(row)


if __name__ == '__main__':
    main()
