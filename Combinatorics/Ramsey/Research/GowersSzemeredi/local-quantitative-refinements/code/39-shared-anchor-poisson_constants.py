#!/usr/bin/env python3
"""Reproduce illustrative Poisson constants with the standard Decimal module.

The exact definitions are the root equation and F_t in the article.
These decimal approximations are separate from the exact finite certificates.
"""
from decimal import Decimal, localcontext
from math import factorial
from pathlib import Path
import csv


def constants(threshold: int) -> tuple[Decimal, Decimal, Decimal]:
    if not isinstance(threshold, int) or threshold < 1:
        raise ValueError('threshold must be a positive integer')
    with localcontext() as ctx:
        ctx.prec = 65
        t = threshold
        def polynomial(x: Decimal) -> Decimal:
            total = term = Decimal(1)
            for j in range(1, t):
                term *= x / Decimal(j)
                total += term
            return total
        lo, hi = Decimal(0), Decimal(t)
        for _ in range(230):
            mid = (lo+hi)/2
            value = polynomial(mid)-mid**t/Decimal(factorial(t-1))
            if value > 0:
                lo = mid
            else:
                hi = mid
        root = (lo+hi)/2
        kappa = root*(-root).exp()*polynomial(root)
        return +root, +kappa, +(1/root)


def main() -> None:
    output = Path(__file__).resolve().parents[1]/'data'/'poisson_constants.csv'
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['threshold','lambda','kappa','transition_q_over_r'])
        for t in range(1,9):
            values=constants(t)
            writer.writerow([t,*(format(x,'.44f') for x in values)])
            print(t,*(format(x,'.12f') for x in values))

if __name__=='__main__':
    main()
