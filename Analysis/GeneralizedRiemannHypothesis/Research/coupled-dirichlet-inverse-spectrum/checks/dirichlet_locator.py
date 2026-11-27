"""Numerical example on the completed real primitive characters mod 3 and 5.

Requires mpmath >= 1.3. Both functions have root number +1. Midpoint
brackets and residual checks here use ordinary multiprecision floating point.
Results are illustrative, and are not certified zero enclosures.
"""
import json
from functools import lru_cache

import mpmath as mp


def completion_pair(t, character, parity):
    q = len(character)
    s = mp.mpc(mp.mpf("0.5"), t)
    z = (s + parity)/2
    normalization = (q/mp.pi)**z * mp.gamma(z)
    value = mp.dirichlet(s, character)
    derivative = mp.dirichlet(s, character, derivative=1)
    gamma_log_derivative = (mp.log(q/mp.pi) + mp.digamma(z))/2
    # Taking the t derivative contributes a factor of i. For conditioning
    # multiply BOTH rows by the same nonzero scale, after differentiation.
    scale = mp.exp(mp.pi*t/4)
    f = normalization * value
    df = 1j * normalization * (derivative + gamma_log_derivative*value)
    assert abs(f.imag * scale) + abs(df.imag * scale) < mp.mpf("1e-20")
    return f.real*scale, df.real*scale


@lru_cache(maxsize=256)
def columns(t):
    u, du = completion_pair(t, (0, 1, -1), 1)
    v, dv = completion_pair(t, (0, 1, -1, -1, 1), 0)
    return [du*dv, du*v, u*dv, u*v]


def normalized_value(t):
    row = columns(t)
    return mp.fdot(row, [1, 3, 2, 5]) / max(map(abs, row))


def find_sample():
    lo = mp.mpf(1)
    roots = []
    step = mp.mpf("0.25")
    for j in range(1, 161):
        hi = 1 + step*j
        if normalized_value(lo)*normalized_value(hi) < 0:
            root = mp.findroot(normalized_value, (lo, hi), tol=mp.mpf("1e-32"))
            assert lo < root < hi and abs(normalized_value(root)) < mp.mpf("1e-27")
            roots.append(root)
            if len(roots) == 9:
                return roots
        lo = hi
    raise ValueError("Insufficient sign changes")


def main():
    mp.mp.dps = 45
    true_sample = find_sample()
    false_t = mp.mpf("4.25")
    assert abs(normalized_value(false_t)) > mp.mpf("0.01")
    observed = sorted(true_sample[:3] + true_sample[4:] + [false_t])
    # W = t + b; Q_j = a_j + d_j*t. Use every observed location.
    equations = []
    rhs = []
    for t in observed:
        row = columns(t)
        row = [v/max(map(abs, row)) for v in row]
        equations.append([row[0]] + [v*t**k for v in row[1:] for k in (0, 1)])
        rhs.append(-t*row[0])
    solution, residual = mp.qr_solve(mp.matrix(equations), mp.matrix(rhs))
    recovered = [1] + [solution[i] for i in (2, 4, 6)]
    quot_remainders = [solution[j] - solution[j+1]*solution[0] for j in (1, 3, 5)]
    assert max(abs(a-b) for a, b in zip(recovered, [1, 3, 2, 5])) < mp.mpf("1e-25")
    assert abs(solution[0]+false_t) < mp.mpf("1e-25")
    assert max(map(abs, quot_remainders)) < mp.mpf("1e-25")
    fmt = lambda v: mp.nstr(v, 27)
    print(json.dumps({
        "arithmetic": "illustrative floating point; 45 decimal working digits",
        "column_order": ["both", "first", "second", "neither"],
        "matrix": [[2,1],[1,3]],
        "true_sample": list(map(fmt, true_sample)),
        "erased": fmt(true_sample[3]), "inserted": fmt(false_t),
        "recovered_false_location": fmt(-solution[0]),
        "recovered_coefficients": list(map(fmt, recovered)),
        "least_squares_residual": fmt(residual),
        "max_division_remainder": fmt(max(map(abs, quot_remainders)))
    }, indent=2))


if __name__ == "__main__":
    main()
