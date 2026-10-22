"""Independently authored supplementary tests; executes no received code."""
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path
from random import Random

rng = Random(20261022)
report = {"scope": "Finite supplements to the written proof, not compiler verification."}

# Exact chi divisibility theorem for integral Pell first coordinates.
chi_checks = 0
for base in range(2, 31):
    xs = [1, base]
    ys = [0, 1]
    for n in range(2, 101):
        xs.append(2 * base * xs[-1] - xs[-2])
        ys.append(2 * base * ys[-1] - ys[-2])
    for m in range(1, 26):
        for n in range(1, 101):
            actual = xs[n] % xs[m] == 0
            expected = n % (2 * m) == m
            assert actual == expected, (base, m, n)
            if actual:
                assert ys[n] % ys[m] == 0
            chi_checks += 1
report["chi_divisibility_checks"] = chi_checks

# Enumerate exactly, without floating point, rational auxiliary Pell roots.
sat_checks = 0
rational_roots = 0
for S in range(2, 151):
    for V in range(1, 301):
        square = Fraction(S * S * V * V - 1, S * S - 1)
        np, nq = isqrt(square.numerator), isqrt(square.denominator)
        if np * np == square.numerator and nq * nq == square.denominator:
            assert nq == 1, (S, V, square)
            rational_roots += 1
        sat_checks += 1
report["rational_auxiliary_cases"] = sat_checks
report["rational_roots_found_all_integral"] = rational_roots

# Sign-safe bound, including zero scale and zero/signed auxiliary quotient.
bound_checks = 0
positive_scale_checks = 0
for case in range(5000):
    q = rng.randrange(16, 65)
    s = rng.randrange(1, 10)
    eta, zeta = rng.randrange(1, 10), rng.randrange(1, 10)
    w0 = rng.randrange(-4, 5)
    i = 2 * rng.randrange(-5, 6) + 1
    T = rng.randrange(-5, 6)
    R = rng.randrange(1, q ** 3)
    X, Y = w0 * w0 * q, s * q ** 3
    E, k = X * Y, eta + zeta
    c, a = k * Y + eta, E + Y
    H, Delta = 4 * a + 3, (a + 2) ** 2 - 1
    L = E * k * Y
    A1, A2 = 1 + L * (L + k), 1 + Delta * c * c
    S = Delta * i * c * c
    Q, D = S * S, 1 + Delta * i * i * c ** 4
    d, v, b = Q - 1, c * T, c + R * D
    e, B = Q * (D * v * v + b * b) - 1, 2 * Q * v * b
    W = 2 * d * ((S * i) * (v * T) + b)
    P, K, u = H * W, H * W + 1, 6 * H * W
    assert D < Q and W > 0 and P >= 14
    assert W * W > d * (e + abs(B) * abs(S))
    assert K > P and A2 > 1
    if w0 != 0:
        assert A2 < 16 * A1
        assert u - 4 * K > P
        positive_scale_checks += 1
    else:
        assert A1 == 1
    bound_checks += 1
report["signed_bound_checks"] = bound_checks
report["positive_scale_separation_checks"] = positive_scale_checks

# Independent rank-four multiplication modulo four for the product guard.
def mul(x, y, a, g):
    out = [0, 0, 0, 0]
    for ix, vx in enumerate(x):
        for iy, vy in enumerate(y):
            coeff = vx * vy
            if (ix & iy) & 1:
                coeff *= a
            if (ix & iy) & 2:
                coeff *= g
            out[ix ^ iy] = (out[ix ^ iy] + coeff) % 4
    return out

def norm(x, a, g):
    out = [1, 0, 0, 0]
    for er, eg in ((1, 1), (-1, 1), (1, -1), (-1, -1)):
        out = mul(out, [x[0], er*x[1], eg*x[2], er*eg*x[3]], a, g)
    return out

for _ in range(5000):
    a, g, Z, u, K, H, d, e, D = [rng.randrange(-20, 21) for _ in range(9)]
    B = 2 * rng.randrange(-20, 21)
    lin = [Z, -u, -K, 0]
    C = mul(lin, lin, a, g)
    C[0] = (C[0] - H*H*d*e) % 4
    F = mul(C, C, a, g)
    F[0] = (F[0] - H**4*d*d*B*B*D) % 4
    nc, nf = norm(C, a, g), norm(F, a, g)
    assert nc[1:] == [0, 0, 0] and nf[1:] == [0, 0, 0]
    assert nf[0] == nc[0] * nc[0] % 4
    assert nf[0] in (0, 1)
report["mod_four_norm_checks"] = 5000

# Record the exact counterexample to the obsolete completeness-index shortcut.
a, H, R, c = 2, 11, 3, 63
A, Delta, m = a + 2, (a + 2) ** 2 - 1, 2 * c * R * H
x, y = 1, 0
for _ in range(m):
    x, y = (A*x + Delta*y) % H, (x + A*y) % H
assert (x, y) == (9, 3)
report["obsolete_index_counterexample"] = {
    "a": a, "H": H, "R": R, "c": c, "m": m,
    "chi_mod_H": x, "psi_mod_H": y,
}

report["status"] = "PASS"
path = Path(__file__).with_name("FINAL_MATH_INDEPENDENT_CHECKS.json")
path.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
