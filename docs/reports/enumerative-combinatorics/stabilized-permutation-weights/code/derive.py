#!/usr/bin/env python3
"""Derive W_d exactly from finite exponential spectra (requires SymPy).

Run from any directory: python code/derive.py --max-d 6
All rational operations are in QQ(q). The construction verifies the ODE
coefficients and the initial condition before exporting any result.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp
from sympy.polys.domains import QQ
from sympy.polys.fields import field

ROOT = Path(__file__).resolve().parents[1]
K, q = field("q", QQ)
qs, t = sp.symbols("q t")
Key = Tuple[int, ...]


def add_frequency(u: Key, v: Key) -> Key:
    return tuple((u[i] if i < len(u) else 0) + (v[i] if i < len(v) else 0)
                 for i in range(max(len(u), len(v))))


def frequency(u: Key):
    return sum((q**j*c for j, c in enumerate(u)), K.zero)


def accumulate(result, key, value):
    if value:
        result[key] = result.get(key, K.zero) + value
        if not result[key]:
            del result[key]


def universal_spectrum(d: int):
    """All vectors c with 1 <= sum((j+1)c_j) <= d+1."""
    out = set()
    def visit(j, remaining, prefix):
        if j == d+1:
            v = list(prefix)
            while v and v[-1] == 0:
                v.pop()
            if v:
                out.add(tuple(v))
            return
        for c in range(remaining//(j+1)+1):
            visit(j+1, remaining-(j+1)*c, prefix+[c])
    visit(0, d+1, [])
    return out


def integer_coefficients(poly):
    result = []
    for i in range(poly.degree()+1):
        value = poly.nth(i)
        if value.q != 1:
            raise ArithmeticError("Expected an integral polynomial.")
        result.append(int(value))
    return result


def rational_tail(coefficient, d):
    # Reverse numerator and denominator directly. Substituting q=1/t into
    # a large expanded symbolic expression creates avoidable expression swell.
    n, z = map(lambda x: sp.Poly(x, qs), sp.fraction(coefficient.as_expr()))
    shift = z.degree()-n.degree()-d*(d+1)
    if shift < 0:
        raise ArithmeticError("The proved regularity at t=0 failed.")
    p = sp.Poly(sum(n.nth(i)*t**(n.degree()-i+shift)
                    for i in range(n.degree()+1)), t)
    den = sp.Poly(sum(z.nth(i)*t**(z.degree()-i)
                      for i in range(z.degree()+1)), t)
    unit = den.nth(0)
    p, den = sp.Poly(p.as_expr()/unit, t), sp.Poly(den.as_expr()/unit, t)
    assert sp.gcd(p, den).degree() == 0
    return p, den


def derive(max_d: int):
    spectra = [{(1,): K.one}]
    records = []
    certificate = []
    for d in range(1, max_d+1):
        start = time.perf_counter()
        rhs = {}
        for a in range(d):
            b = d-1-a
            for u, c in spectra[a].items():
                for v, e in spectra[b].items():
                    accumulate(rhs, add_frequency(u, v), q**b*c*e)
        for u, c in spectra[d-1].items():
            accumulate(rhs, u, -q**(d-1)*c)
        current = {u: c/(frequency(u)-q**d) for u, c in rhs.items()}
        leading = (0,)*d+(1,)
        current[leading] = -sum(current.values(), K.zero)
        # Independent algebraic identity checks on the constructed expression.
        assert sum(current.values(), K.zero) == 0
        for u, c in current.items():
            assert (frequency(u)-q**d)*c == rhs.get(u, K.zero)
        allowed = universal_spectrum(d)
        assert set(current).issubset(allowed)
        spectra.append(current)
        p, den = rational_tail(current[leading], d)
        universal_denominator = sp.Poly(1, t)
        factors = []
        for u in sorted(allowed-{leading}, key=lambda k: (len(k), k)):
            factor = 1-sum(c*t**(d-j) for j, c in enumerate(u))
            universal_denominator *= sp.Poly(factor, t)
            factors.append(sp.sstr(factor))
        cancellation = universal_denominator.exquo(den)
        record = {
            "d": d,
            "spectrum_size": len(current),
            "universal_spectrum_size": len(allowed),
            "P": integer_coefficients(p),
            "Q": integer_coefficients(den),
            "universal_denominator_degree": universal_denominator.degree(),
            "cancellation_factor": sp.sstr(sp.factor(cancellation.as_expr())),
            "spectrum": [list(u) for u in sorted(current)],
            "denominator_factors": factors,
        }
        records.append(record)
        certificate.append({
            "d": d,
            "terms": [{"frequency_coefficients": list(u),
                       "amplitude": sp.sstr(c.as_expr())}
                      for u, c in sorted(current.items())],
            "ode_residual": "0 (checked in QQ(q))",
            "initial_value": "0 (checked in QQ(q))",
        })
        print(f"d={d}: {len(current)} frequencies, denominator degree {den.degree()}, "
              f"all exact identities passed ({time.perf_counter()-start:.3f}s).", flush=True)
    return records, certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-d", type=int, default=6)
    parser.add_argument("--check-only", action="store_true",
                        help="Compare P,Q with packaged data instead of rewriting it.")
    args = parser.parse_args()
    if args.max_d < 1:
        parser.error("max-d must be positive")
    records, certificate = derive(args.max_d)
    path = ROOT/"data/rational_series.json"
    if args.check_only:
        old = {r["d"]: r for r in json.loads(path.read_text())}
        for r in records:
            assert r["P"] == old[r["d"]]["P"]
            assert r["Q"] == old[r["d"]]["Q"]
        print("Every derived numerator and denominator matches the packaged data.")
    else:
        path.write_text(json.dumps(records, indent=2)+"\n")
        (ROOT/"data/spectral_certificates.json").write_text(
            json.dumps(certificate, indent=2)+"\n")
    print("SymPy version:", sp.__version__)


if __name__ == "__main__":
    main()
