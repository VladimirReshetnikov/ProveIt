#!/usr/bin/env python3
"""Uncertified finite-tail constants, using only Python's decimal module.

Working precision and a finite coefficient cutoff are not interval error bounds.
The calculation includes the corrected cubic coefficient tau in 1-R.
"""
import argparse
from decimal import Decimal, localcontext
from pathlib import Path
from output_json import emit_json, prepare_output
from third_sector import integer_range, require, rooted_counts


def evaluate(coefficients, x):
    value = Decimal(0)
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def derivative(coefficients):
    return [i * coefficients[i] for i in range(1, len(coefficients))]


def decimal_pi(digits):
    # Quadratically convergent arithmetic-geometric-mean algorithm.
    a, b, t, p = Decimal(1), Decimal(1) / Decimal(2).sqrt(), Decimal(1) / 4, Decimal(1)
    for _ in range(digits.bit_length() + 2):
        next_a = (a + b) / 2
        b = (a * b).sqrt()
        t -= p * (a - next_a) ** 2
        a = next_a
        p *= 2
    return (a + b) ** 2 / (4 * t)


def compute(tail=360, digits=70):
    integer_range('numeric tail cutoff', tail, 32, 480)
    integer_range('working decimal precision', digits, 40, 200)
    with localcontext() as context:
        context.prec = digits
        rooted = rooted_counts(tail + 3)
        def analytic_tail(shift):
            out = [Decimal(0)] * (tail + 1)
            for q in range(2, tail + 1):
                for n in range(1, tail // q + 1):
                    out[q * n] += Decimal(rooted[n + shift]) / q
            return out
        E, Htail, J2tail, J3tail = [analytic_tail(shift) for shift in range(4)]
        Ep, Epp = derivative(E), derivative(derivative(E))
        rho = Decimal('0.3383')
        for _ in range(digits.bit_length() + 4):
            residual = rho.ln() + 1 + evaluate(E, rho)
            rho -= residual / (1 / rho + evaluate(Ep, rho))
        residual = rho.ln() + 1 + evaluate(E, rho)
        require(abs(residual) < Decimal(10) ** (10 - digits), 'numeric root residual too large')
        beta = (2 * (1 + rho * evaluate(Ep, rho))).sqrt()
        C = (1 / rho - 1 + evaluate(Htail, rho)).exp()
        J3 = ((1 - rho - rho * rho - 2 * rho ** 3) / rho ** 3 + evaluate(J3tail, rho)).exp()
        a = C / (1 - rho)
        c = ((1 - rho - rho * rho) / (rho * rho) + evaluate(J2tail, rho)).exp() / ((1 - rho) * (1 - rho * rho))
        tau = beta ** 3 / 36 + (1 - rho * rho * evaluate(Epp, rho)) / (2 * beta)
        eta = 1 / rho - rho * evaluate(derivative(Htail), rho) - rho / (1 - rho)
        x = rho * rho
        rx = evaluate([Decimal(v) for v in rooted], x)
        hx = (evaluate([Decimal(0)] + [Decimal(rooted[n + 1]) for n in range(1, len(rooted) - 1)], x)
              + evaluate(Htail, x)).exp()
        d2 = hx / ((1 - x) * (1 - rx))
        M = 3 * eta / 2 + beta * beta * (Decimal(1) / 18 + 1 / rho - 3 / (4 * rho * rho)) - 5 * tau / (2 * beta)
        u5 = rho * rho * (1 - rho ** 3) * a ** 3 / (2 * beta ** 5)
        u3 = (rho * rho * (1 - rho ** 3) * (a ** 3 * M / beta ** 5 + a * (c - d2 / 2) / beta ** 3)
              + (-2 * rho * rho + 5 * rho ** 5) * a ** 3 / (2 * beta ** 5))
        sqrt_pi = decimal_pi(digits).sqrt()
        Au = u5 / (3 * sqrt_pi / 4)
        Av = rho ** 3 * J3 / ((1 - rho) * (1 - rho * rho) * beta * sqrt_pi)
        ratio = Av / Au
        q1 = Decimal(15) / 8 + 3 * u3 / (2 * u5)
        values = {'rho': rho, 'beta': beta, 'C': C, 'J3': J3, 'tau': tau, 'eta': eta,
                  'A_U': Au, 'A_V': Av, 'A_V_over_A_U': ratio, 'u_minus5': u5,
                  'u_minus3': u3, 'U_relative_first_correction': q1}
        displayed = min(45, digits - 10)
        return {'status': 'computed', 'arithmetic': 'Python standard-library Decimal',
                'tail_cutoff': tail, 'working_digits': digits,
                'qualification': 'Uncertified finite-tail evaluation; displayed digits have no interval error certificate.',
                'values': {name: format(value, f'.{displayed}g') for name, value in values.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tail', type=int, default=360, help='32..480; default 360')
    parser.add_argument('--digits', type=int, default=70, help='40..200; default 70')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    prepare_output(parser, args.output)
    try:
        result = compute(args.tail, args.digits)
    except (ValueError, ArithmeticError) as error:
        parser.exit(2, f'numeric error: {error}\n')
    emit_json(parser, result, args.output)


if __name__ == '__main__':
    main()
