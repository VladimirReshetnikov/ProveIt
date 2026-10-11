"""Independent finite and convergent checks of the transverse harmonic identities.

These are arbitrary-precision diagnostics, not interval certificates.  The
convergent depth-two comparison uses direct elementary prefix sums on its
H side and independently evaluated Hurwitz jets on its paired-tail side.
No infinite-depth theorem is inferred from the finite checks.
"""

import json
from pathlib import Path

import mpmath as mp


mp.mp.dps = 65
L = mp.log(2 * mp.pi)
out = {"dps": mp.mp.dps, "kind": "non-interval diagnostics", "checks": []}


def fmt(z):
    return mp.nstr(z, 32)


def ell(m, r, x):
    if m == 0 and r == 1:
        return mp.loggamma(x) - L / 2
    return mp.diff(lambda u: mp.zeta(u, x), -m, r)


def h_jet(u, r, a, b):
    return mp.diff(lambda v: mp.zeta(v, b) - mp.zeta(v, a), u, r)


def check(name, lhs, rhs, tolerance, **metadata):
    residual = abs(lhs - rhs)
    record = {"name": name, "left": fmt(lhs), "right": fmt(rhs),
              "absolute_residual": fmt(residual), "tolerance": str(tolerance),
              "passed": bool(residual < mp.mpf(tolerance)), **metadata}
    out["checks"].append(record)
    if not record["passed"]:
        raise AssertionError(record)


def triple_prefix(s, t, m, r, b, N):
    xs = [b + n for n in range(N)]
    direct = mp.mpc(0)
    for i in range(N):
        for j in range(i):
            for k in range(j):
                direct += xs[i] ** (-s) * xs[j] ** m * (-mp.log(xs[j])) ** r * xs[k] ** (-t)
    gap = mp.mpc(0)
    for i in range(N):
        for k in range(i):
            gap += xs[i] ** (-s) * xs[k] ** (-t) * (ell(m, r, xs[k] + 1) - ell(m, r, xs[i]))
    return direct, gap


for m, r, N in [(0, 1, 7), (0, 2, 6), (1, 1, 7), (2, 2, 5)]:
    b = mp.mpf("0.7")
    s, t = mp.mpc("1.3", ".2"), mp.mpc(".9", "-.1")
    direct, gap = triple_prefix(s, t, m, r, b, N)
    check(f"finite triple m={m}, r={r}, N={N}", direct, gap, "1e-59")


def prefix_zeta_jet(s, m, r, a, N):
    """Truncate the original nested sum, differentiating the finite inner sum."""
    prefix = mp.mpf(0)
    value = mp.mpc(0)
    for n in range(N):
        x = n + a
        value += x ** (-s) * prefix
        prefix += x ** m * (-mp.log(x)) ** r
    return value


for a, b, s, N in [
    (mp.mpf("1.3"), mp.mpf("0.65"), mp.mpf("20.5"), 280),
    (mp.mpf("0.8"), mp.mpf("1.15"), mp.mpc("21.2", ".3"), 260),
]:
    m, r = 0, 1
    paired = mp.fsum([(n+b)**(-s) * ell(m, r, n+b)
                       - (n+a)**(-s) * ell(m, r, n+a) for n in range(N)])
    hs = mp.zeta(s, b) - mp.zeta(s, a)
    Hjet = (prefix_zeta_jet(s, m, r, b, N)
            - prefix_zeta_jet(s, m, r, a, N)
            - mp.zeta(s, a) * (ell(m, r, b)-ell(m, r, a)))
    predicted = ell(m, r, b) * hs - Hjet
    check("noninteger endpoints: convergent paired tail versus ordered H derivative",
          paired, predicted, "1e-41", a=fmt(a), b=fmt(b), s=fmt(s), truncation=N,
          note="Finite truncation discrepancy is retained; tolerance is diagnostic.")


def negative_formula(m, r, d, a, b):
    q = d + 1
    value = mp.bernpoly(q, a) * ell(m, r, a) - mp.bernpoly(q, b) * ell(m, r, b)
    for k in range(q + 1):
        value += mp.binomial(q, k) * mp.bernpoly(q-k, 1) * h_jet(-m-k, r, a, b)
    return value / q


for a, b in [(mp.mpf("1.3"), mp.mpf("0.65")),
             (mp.mpf("0.8"), mp.mpf("1.15")),
             (mp.mpf("2.2"), mp.mpf("1.4"))]:
    bernoulli = negative_formula(0, 1, 0, a, b)
    barnes = mp.log(mp.barnesg(a)) - mp.log(mp.barnesg(b)) - (a-b)*L/2
    check("noninteger endpoints: D_0,1(0) in Barnes G", bernoulli, barnes, "1e-59",
          a=fmt(a), b=fmt(b))


for m, r, d, N in [(0, 1, 0, 4), (0, 1, 3, 4), (1, 1, 2, 4),
                    (2, 2, 1, 3), (2, 0, 3, 4)]:
    b = mp.mpf("0.7")
    a = b + N
    finite_interval = mp.fsum([(b+n)**d * ell(m, r, b+n) for n in range(N)])
    bernoulli = negative_formula(m, r, d, a, b)
    check(f"negative exponent Bernoulli formula m={m}, r={r}, d={d}",
          finite_interval, bernoulli, "1e-56", interval_length=N)


# This is intentionally a disagreement, illustrating the lost endpoint term.
a, b = mp.mpf("2"), mp.mpf("1")
continued = (mp.digamma(a)-mp.digamma(b))/2 - (a-b)
direct_boundary = (mp.digamma(a)-mp.digamma(b))/2
check("boundary anomaly: direct minus continued = a-b", direct_boundary-continued,
      a-b, "1e-60", direct_boundary=fmt(direct_boundary), continued=fmt(continued),
      explanation="At s=1, m=r=0, constant summands cancel before summing; analytic continuation retains their finite endpoint term.")

out["all_passed"] = all(c["passed"] for c in out["checks"])
out["check_count"] = len(out["checks"])
(Path(__file__).resolve().parents[1] / "results" / "verify_r8_audit.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"all_passed": out["all_passed"], "check_count": out["check_count"],
                  "max_residual": max(float(c["absolute_residual"]) for c in out["checks"])}))
