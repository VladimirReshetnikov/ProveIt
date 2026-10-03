#!/usr/bin/env python3
"""Lambert-W index inversion for A189281 and A110128 (mpmath required).

This approximates the real index associated with a count. Rounding to an exact
integer threshold is not certified by an asymptotic estimate alone.
"""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp


def approximate_index(y: int, theta: int = 1) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Return the Lambert backbone, constant-corrected, and 1/z-corrected values."""
    if y <= 1 or theta not in (1, 2):
        raise ValueError('Require y>1 and theta in {1,2}')
    L = mp.log(y)
    z = L / mp.lambertw(L / mp.e)
    w = mp.log(z)
    kappa = mp.log(2 * mp.pi) / 2 - theta
    c1 = 3 if theta == 1 else 4
    x0 = z - mp.mpf('0.5') - kappa/w
    x1 = x0 - ((c1 - mp.mpf(1)/24)/w + kappa**2/(2*w**3))/z
    return z, x0, x1


def main() -> None:
    mp.mp.dps = 80
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root/'data'/'exact_values.json').read_text())
    print('Numerical diagnostics only; inputs are exact enumerated counts.')
    for theta in (1, 2):
        for n in (12, 16, 20):
            approximations = approximate_index(data[str(theta)][n], theta)
            errors = [mp.nstr(x-n, 14) for x in approximations]
            print(f'theta={theta}, n={n}: index errors {errors}')


if __name__ == '__main__':
    main()
