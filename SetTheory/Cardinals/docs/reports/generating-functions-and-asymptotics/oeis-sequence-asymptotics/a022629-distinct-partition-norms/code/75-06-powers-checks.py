"""Independent exact finite checks; run with `python checks.py`.

These tests compare the product algorithm to a divisor-sum recurrence,
convolution, and initial values. They do not certify analytic limits.
"""
from __future__ import annotations
import json
import platform
from pathlib import Path
import numpy
import scipy
import sympy
from numerics import exact_coefficients


def recurrence_coefficients(nmax: int, r: int, s: int) -> list[int]:
    beta = [0] * (nmax + 1)
    for k in range(1, nmax + 1):
        for h in range(1, nmax // k + 1):
            beta[k * h] += (-1)**(h-1) * k**(1+r*h)
    a = [1]
    for n in range(1, nmax + 1):
        numerator = s * sum(beta[j] * a[n-j] for j in range(1, n+1))
        quotient, remainder = divmod(numerator, n)
        assert remainder == 0, (r, s, n)
        a.append(quotient)
    return a


def main() -> None:
    checks = []
    for r in (1, 2, 3):
        for s in (1, 2, 3):
            assert exact_coefficients(120, r, s) == recurrence_coefficients(120, r, s)
            checks.append(f'Product = independent recurrence through n=120, r={r}, s={s}')
    a = exact_coefficients(200)
    convolution = [sum(a[k] * a[n-k] for k in range(n+1)) for n in range(201)]
    assert convolution == exact_coefficients(200, 1, 2)
    checks.append('Two-layer product = self-convolution through n=200')
    assert exact_coefficients(6, 2, 1) == [1, 1, 4, 13, 25, 77, 161]
    assert exact_coefficients(5, 3, 1) == [1, 1, 8, 35, 91, 405]
    checks.append('Initial second and third norm-moment coefficients match array entries')
    for invalid in [(-1, 1, 1), (5, 1.5, 1), (5, 1, 0)]:
        try:
            exact_coefficients(*invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(f'Invalid parameters accepted: {invalid}')
    checks.append('Input validation rejects invalid exact-arithmetic parameters')
    result = {'status': 'PASS', 'checks': checks,
              'environment': {'python': platform.python_version(),
                              'numpy': numpy.__version__, 'scipy': scipy.__version__,
                              'sympy': sympy.__version__}}
    (Path(__file__).resolve().parent / 'verification_results.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
