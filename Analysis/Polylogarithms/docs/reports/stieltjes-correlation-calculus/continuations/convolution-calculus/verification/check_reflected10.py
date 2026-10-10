"""Independent real-quadrature check of the mixed reflected correlation."""

import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 45
CENTER = mp.mpf(3) / 2
N = 120
COEFFICIENTS = [mp.stieltjes(1, CENTER)]
harmonic = mp.mpf(0)
for k in range(1, N + 1):
    harmonic += mp.mpf(1) / k
    z = mp.zeta(k + 1, CENTER)
    dz = mp.diff(lambda s: mp.zeta(s, CENTER), k + 1)
    COEFFICIENTS.append(-(-1)**k * (harmonic * z + dz))


def g0(x):
    return -mp.digamma(x)


def smooth_g1(x):
    """gamma_1(1+x), for x in [0,1], by a convergent Taylor series."""
    return mp.polyval(list(reversed(COEFFICIENTS)), x - mp.mpf("0.5"))


def g1(x):
    return mp.log(x) / x + smooth_g1(x)


def reflected10(a):
    h = a / 2
    ca = g0(a)
    da = g1(a)
    dga = mp.zeta(2, a) + mp.diff(lambda s: mp.zeta(s, a), 2)

    def fleft(x):
        if x < mp.mpf("1e-35"):
            ratio = mp.polygamma(1, a)
        else:
            ratio = (g0(a - x) - ca) / x
        return ratio * mp.log(x) + smooth_g1(x) * g0(a - x)

    def fright(y):
        if y < mp.mpf("1e-35"):
            ratio = -dga
        else:
            ratio = (g1(a - y) - da) / y
        return ratio + g1(a - y) * g0(1 + y)

    return (mp.quad(fleft, [0, h / 2, h]) + ca * mp.log(h)**2 / 2
            + mp.quad(fright, [0, h / 2, h]) + da * mp.log(h)
            + mp.quad(lambda x: g1(x) * g0(1 + a - x), [a, (1 + a) / 2, 1]))


def circular10(a):
    b = 1 - a
    ca = g0(a)
    db = g1(b)
    dgb = mp.zeta(2, b) + mp.diff(lambda s: mp.zeta(s, b), 2)

    def first(x):
        ratio = -mp.polygamma(1, a) if x < mp.mpf("1e-35") else (g0(a + x) - ca) / x
        return ratio * mp.log(x) + smooth_g1(x) * g0(a + x)

    def second(y):
        ratio = dgb if y < mp.mpf("1e-35") else (g1(b + y) - db) / y
        return ratio + g1(b + y) * g0(1 + y)

    return (mp.quad(first, [0, b / 2, b]) + ca * mp.log(b)**2 / 2
            + mp.quad(second, [0, a / 2, a]) + db * mp.log(a))


if __name__ == "__main__":
    rows = []
    for a in [mp.mpf(1) / 2, mp.sqrt(2) - 1]:
        b = 1 - a
        cases = [
            ("reflected10", reflected10(a),
             mp.mpf(3) / 2 * mp.stieltjes(2, a) - g0(a) * mp.zeta(2) - mp.zeta(3)),
            ("circular10", circular10(a),
             mp.stieltjes(2, a) / 2 + mp.stieltjes(2, b)
             + mp.zeta(2) * (g0(a) + g0(b)) - mp.zeta(3)),
        ]
        for kind, lhs, rhs in cases:
            row = dict(kind=kind, a=mp.nstr(a, 42), integral=mp.nstr(lhs, 42),
                       formula=mp.nstr(rhs, 42), absolute_error=mp.nstr(abs(lhs - rhs), 7),
                       gamma1_series_check=mp.nstr(abs(g1(a) - mp.stieltjes(1, a)), 7))
            rows.append(row)
            print(json.dumps(row), flush=True)
    Path(__file__).with_name("results10.json").write_text(json.dumps(rows, indent=2) + "\n")
