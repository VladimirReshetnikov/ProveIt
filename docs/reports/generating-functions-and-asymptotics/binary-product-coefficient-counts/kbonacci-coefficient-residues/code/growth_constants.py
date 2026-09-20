"""Regenerate illustrative growth constants by floating-point bisection.

These approximations are NOT used in the exact proof or verification suite.
"""
from __future__ import annotations

import csv
from pathlib import Path
from typing import Callable


def root_on_unit_interval(function: Callable[[float], float]) -> float:
    left, right = 0.0, 1.0
    if not function(left) > 0 > function(right):
        raise ValueError('expected a strictly bracketed root')
    for _ in range(80):
        middle = (left + right)/2
        if function(middle) > 0:
            left = middle
        else:
            right = middle
    return (left + right)/2


def main() -> None:
    rows = []
    for k in (2,3,4,5,6,8,10):
        t = root_on_unit_interval(lambda z: 1-sum(z**j for j in range(1,k+1)))
        r = root_on_unit_interval(lambda z: 1-2*z+2*z**k-2*z**(k+1))
        derivative = -2+2*k*r**(k-1)-2*(k+1)*r**k
        gamma = -(1+2*r**k)/(r*derivative)
        rows.append([k,1/t,1/r,gamma])
    destination = Path(__file__).resolve().parent.parent/'data/growth_constants.csv'
    destination.parent.mkdir(parents=True,exist_ok=True)
    with destination.open('w',newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['k','beta_support','rho_odd','leading_constant_odd'])
        writer.writerows(rows)
    print(destination)


if __name__ == '__main__':
    main()
