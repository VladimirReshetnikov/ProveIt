#!/usr/bin/env python3
"""Exact finite checks for the erasure-sensitive arrangement proof.

These checks supplement, and do not replace, the written finite-group proof.
"""
from fractions import Fraction as F
from collections import Counter
from itertools import product
from math import comb, sqrt
import json
from pathlib import Path


def conv(a, b, n, q=1):
    out = Counter()
    for (x, z), av in a.items():
        for (y, w), bv in b.items():
            out[((x + y) % n, (z + w) % q)] += av * bv
    return out


def counts(table, n, m, q=2, s=4):
    """Ambient-normalized valid and valid-failed counts."""
    valid = respected = 0
    for h in range(m):
        edges = Counter()
        domains = Counter()
        for x in range(n):
            for y in range(m):
                a = table[x * m + y]
                b = table[x * m + (y + h) % m]
                if a is not None and b is not None:
                    edges[x, (b - a) % q] += 1
                    domains[x, 0] += 1
        ep, dp = Counter({(0, 0): 1}), Counter({(0, 0): 1})
        for _ in range(s // 2):
            ep = conv(ep, edges, n, q)
            dp = conv(dp, domains, n)
        respected += sum(v * v for v in ep.values())
        valid += sum(v * v for v in dp.values())
    total = n ** (s - 1) * m ** (s + 1)
    return F(valid, total), F(valid - respected, total)


def best_model_profile(table, n, m, q=2):
    best = None
    for b in range(q):
        if (n * b) % q or (m * b) % q:
            continue
        for c in range(q):
            if (m * c) % q:
                continue
            sizes, errors, collision = [], [], []
            for x in range(n):
                hist = Counter(
                    (table[x * m + y] - (b * x + c) * y) % q
                    for y in range(m) if table[x * m + y] is not None
                )
                size = sum(hist.values())
                err = size - max(hist.values(), default=0)
                sizes.append(F(size, m))
                errors.append(F(err, m))
                collision.append(F(size * size - sum(v * v for v in hist.values()), m*m))
            score = sum(errors, F(0)) / n
            if best is None or score < best[0]:
                best = score, sizes, errors, collision
    d, sizes, errors, collision = best
    tau = 1 - sum(sizes, F(0)) / n
    mass = sum((a * e for a, e in zip(sizes, errors)), F(0)) / n
    gamma = sum(collision, F(0)) / n
    return d, tau, mass, gamma


def exhaustive():
    records = []
    total = 0
    for n, m in [(2, 2), (2, 3), (3, 2)]:
        count = 0
        for table in product((None, 0, 1), repeat=n*m):
            lam, theta = counts(table, n, m)
            d, tau, mass, gamma = best_model_profile(table, n, m)
            assert lam <= 1 - tau
            assert lam >= 1 - 8 * tau
            assert gamma >= mass
            assert d*d <= mass * (d + tau/F(2))
            factor = 1 - 6 * (d + tau)
            if factor >= 0:
                assert theta >= 4 * factor * gamma
                assert theta >= 4 * factor * mass
            count += 1
        records.append({"n": n, "m": m, "partial_labelings": count})
        total += count
    return records, total


def direct_count(table, n, m, s=4):
    valid = failed = 0
    for h in range(m):
        for free in product(range(n), repeat=s-1):
            last = (sum(free[:s//2]) - sum(free[s//2:])) % n
            xs = free + (last,)
            for ys in product(range(m), repeat=s):
                diffs = []
                for x, y in zip(xs, ys):
                    a = table[x*m+y]
                    b = table[x*m+(y+h)%m]
                    if a is None or b is None:
                        break
                    diffs.append((b-a) % 2)
                if len(diffs) == s:
                    valid += 1
                    failed += sum(diffs) % 2
    total = n**(s-1)*m**(s+1)
    return F(valid, total), F(failed, total)


def binary_family(n, m, s):
    nu = F(1, n)
    delta = nu**(s-1) - nu**s
    ps = [comb(s,j)*(nu**j*(1-nu)**(s-j)+(-1)**j*delta) for j in range(s+1)]
    assert all(p >= 0 for p in ps)
    assert sum(ps) == 1
    theta = F(2,m)*sum((ps[j]/m**j for j in range(1,s,2)), F(0))
    lam = ps[0] + sum(((2**j+2)*ps[j]/m**(j+1) for j in range(1,s+1)), F(0))
    d = nu / m
    tau = nu*(1-F(2,m))
    mass = F(2,m)*d
    assert d*d <= mass*(d+tau/F(2))
    # For this uniform exceptional row the Cauchy profile is exact.
    assert d*d == mass*(d+tau/F(2))
    assert theta >= s*(1-2*(s-1)*(d+tau))*mass
    return lam, theta, d, tau, mass


def main():
    exhaustive_records, total = exhaustive()
    crosschecks = []
    for n,m in [(3,3),(3,5),(5,3)]:
        table = [0]*(n*m)
        table[1] = 1
        for y in range(2,m):
            table[y] = None
        a = counts(table,n,m)
        b = direct_count(table,n,m)
        c = binary_family(n,m,4)[:2]
        assert a == b == c
        crosschecks.append({"n":n,"m":m,"lambda":str(a[0]),"theta":str(a[1])})
    activation = []
    for s in (4,6,8,16):
        for n in (100003,1000003):
            for m in (101,1001,10001):
                lam,theta,d,tau,mass = binary_family(n,m,s)
                e = theta + 1-lam
                assert e <= F(1,240*(s-1))
                # Use the rational bound D<=2E/s to avoid any root-rounding checks.
                b_lower = 1-2*(s-1)*(2*e/s+tau)
                assert b_lower >= F(79,80)
                t_upper = theta/(s*b_lower)
                assert mass <= t_upper
                assert d*d <= t_upper*(d+tau/F(2))
                assert d <= t_upper/(F(2,m))
                activation.append({"s":s,"n":n,"m":m,
                    "eta":float(theta/lam),"d":float(d),
                    "theta_kappa_tau_over_s_d2":float(theta*tau/(2*s*d*d)),
                    "d_s_beta_over_theta":float(d*s*F(2,m)/theta)})
    output={"scope":"Exact rational validation; not a replacement for the proof",
        "exhaustive_partial_labelings":total,"exhaustive":exhaustive_records,
        "direct_convolution_formula_crosschecks":crosschecks,
        "nonzero_error_activated_family_cases":len(activation),
        "family_cases":activation,"all_checks_passed":True}
    path=Path(__file__).resolve().parent.parent / "data" / "arrangement_erasure_validation.json"
    path.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps({k:v for k,v in output.items() if k!="family_cases"},indent=2))


if __name__ == "__main__":
    main()
