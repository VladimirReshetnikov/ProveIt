"""Independent exact distribution-rank and analytic L-jet bridge checks.

The proof is algebraic and analytic; these finite checks are regression evidence.
Run with a Python interpreter containing mpmath and sympy.

Default: q=3..60, bridge derivatives through order 5, 65 decimal digits.
--quick: q=3..20, bridge derivatives through order 3.
The JSON report is written to ../data/distributions_and_bridges.json relative
to this script, independently of the current working directory.
"""
import argparse
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
import mpmath as mp
from sympy import factorint, divisors, totient


def rank(rows):
    pivots = {}
    for source in rows:
        row = {j: Fraction(x) for j, x in enumerate(source) if x}
        while row:
            lead = min(row)
            if lead not in pivots:
                scale = row[lead]
                pivots[lead] = {j: x / scale for j, x in row.items()}
                break
            scale = row[lead]
            for j, x in pivots[lead].items():
                v = row.get(j, Fraction(0)) - scale * x
                if v:
                    row[j] = v
                else:
                    row.pop(j, None)
    return len(pivots)


def distribution_rows(q, weight, all_divisors=False):
    ds = [d for d in divisors(q) if d > 1] if all_divisors else factorint(q)
    out = []
    for d in ds:
        t = weight(d)
        for r in range(q // d):
            row = [Fraction(0) for _ in range(q)]
            for j in range(d):
                row[r + j * (q // d)] += 1
            row[(d * r) % q] -= t
            out.append(row)
    return out


def reflection_rows(q, parity):
    out = []
    for r in range(1, q):
        row = [0] * q
        row[r] += 1
        row[(-r) % q] += parity
        out.append(row)
    return out


def check_ranks(maximum_q=60):
    counts = dict(distribution=0, anchored=0, reflected=0, divisor_agreement=0)
    for q in range(3, maximum_q + 1):
        phi = int(totient(q))
        anchor = [[1] + [0] * (q - 1)]
        for s in [-4, -1, 0, 1, 2, 7]:
            rows = distribution_rows(q, lambda d: Fraction(d) ** s)
            assert q - rank(rows) == phi, (q, s, 'full')
            assert q - rank(rows + anchor) == phi - 1, (q, s, 'anchored')
            counts['distribution'] += 1
            counts['anchored'] += 1
            for parity in [-1, 1]:
                expected = phi // 2 - (parity == -1)
                actual = q - rank(rows + anchor + reflection_rows(q, parity))
                assert actual == expected, (q, s, parity, actual, expected)
                counts['reflected'] += 1
            if q <= 30:
                all_rows = distribution_rows(q, lambda d: Fraction(d) ** s, True)
                assert rank(rows + all_rows) == rank(rows)
                counts['divisor_agreement'] += 1
        # Arbitrary independent prime weights, including vanishing weights.
        for target in [0, -1, Fraction(1, 2)]:
            rows = distribution_rows(q, lambda d: target)
            assert q - rank(rows) == phi, (q, target, 'arbitrary primes')
            counts['distribution'] += 1
    return counts


def character(q, generator, exponent):
    vals = [mp.mpc(0) for _ in range(q)]
    order = int(totient(q))
    root = mp.exp(2 * mp.pi * mp.j * exponent / order)
    for j in range(order):
        vals[pow(generator, j, q)] = root ** j
    return vals


def lfun(q, vals):
    return lambda s: q ** (-s) * mp.fsum(vals[a] * mp.zeta(s, mp.mpf(a) / q)
                                         for a in range(1, q) if vals[a])


def logjet(coeffs):
    out = [mp.mpf(0)]
    a0 = coeffs[0]
    for n in range(1, len(coeffs)):
        out.append(coeffs[n] / a0 - mp.fsum(j * out[j] * coeffs[n-j]
                    for j in range(1, n)) / (n * a0))
    return [factorial(n) * x for n, x in enumerate(out)]


def check_bridges(maximum_derivative=5):
    mp.mp.dps = 65
    families = [(3, 2, 1), (4, 3, 1), (5, 2, 1), (7, 3, 2)]
    cases = []
    omitted_conjugation = {}
    for q, g, exp in families:
        vals = character(q, g, exp)
        fun = lfun(q, vals)
        odd = abs(vals[q-1] + 1) < mp.mpf('1e-50')
        for k in [1, 2, 3]:
            nu = int((k % 2) == odd)
            neg = mp.taylor(fun, -k, maximum_derivative + nu)
            if nu:
                assert abs(neg[0]) < mp.mpf('1e-57')
            b = neg[nu:]
            pos = mp.taylor(fun, k + 1, maximum_derivative)
            pos_log, neg_log = logjet(pos), logjet(b)
            errors = []
            for r in range(1, maximum_derivative + 1):
                harmonic = mp.fsum(mp.mpf(j) ** (-r) for j in range(1, k+1))
                if r == 1:
                    known = mp.euler + mp.log(2 * mp.pi / q) - harmonic
                elif r % 2:
                    known = factorial(r-1) * (mp.zeta(r) - harmonic)
                else:
                    eta = (1 - mp.mpf(2) ** (1-r)) * mp.zeta(r)
                    known = factorial(r-1) * (harmonic + (-1) ** nu * eta)
                err = abs(pos_log[r] - (-1) ** r * mp.conj(neg_log[r]) - known)
                assert err < mp.mpf('1e-52'), (q, k, r, err)
                errors.append(err)
            z = mp.mpc('0.13', '0.09')
            bz = fun(-k - mp.conj(z)) / ((-mp.conj(z)) ** nu)
            trig = 1/mp.cos(mp.pi*z/2) if nu == 0 else (mp.pi*z/2)/mp.sin(mp.pi*z/2)
            kernel = (2*mp.pi/q)**z * mp.gamma(k+1)/mp.gamma(k+1+z) * trig
            err = abs(fun(k+1+z)/pos[0] - kernel * mp.conj(bz/b[0]))
            assert err < mp.mpf('1e-52'), (q, k, 'germ', err)
            errors.append(err)
            cases.append(dict(q=q, exponent=exp, k=k, nu=nu,
                              maximum_error=mp.nstr(max(errors), 10)))
            if (q, k) == (5, 1):
                constant = mp.euler + mp.log(2*mp.pi/q) - 1
                wrong = pos_log[1] + neg_log[1] - constant
                omitted_conjugation['q5_odd_first_bridge_defect'] = mp.nstr(wrong, 30)
            if (q, k) == (7, 1):
                wrong = pos_log[2] - neg_log[2] - (1 + mp.pi**2/12)
                omitted_conjugation['q7_even_second_bridge_defect'] = mp.nstr(wrong, 30)
    return dict(cases=cases, omitted_conjugation=omitted_conjugation)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true',
                        help='Use q<=20 and bridge derivatives through order 3.')
    args = parser.parse_args()
    maximum_q = 20 if args.quick else 60
    maximum_derivative = 3 if args.quick else 5
    result = {
        'configuration': {
            'maximum_q': maximum_q,
            'maximum_bridge_derivative': maximum_derivative,
            'decimal_digits': 65,
            'quick': args.quick,
        },
        'rank_checks': check_ranks(maximum_q),
        'bridge_checks': check_bridges(maximum_derivative),
    }
    destination = Path(__file__).resolve().parent.parent / 'data' / 'distributions_and_bridges.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
