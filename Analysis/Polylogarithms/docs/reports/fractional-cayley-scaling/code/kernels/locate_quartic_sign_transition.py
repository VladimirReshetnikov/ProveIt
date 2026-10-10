#!/usr/bin/env python3
"""Locate one quartic-sign zero along K=0; diagnostics only, no uniqueness claim."""
import json
from pathlib import Path
import mpmath as mp


def threshold_and_quartic(b):
    A = 1+mp.power(2, -b)
    B = A+mp.power(3, -b)
    C = B+mp.power(4, -b)
    G = lambda a: C+A**3*(mp.mpf(20)/27)**a-2*A*B*(mp.mpf(5)/6)**a
    a = mp.findroot(G, (1, 2))
    p = {n: mp.fsum(mp.power(k, -b) for k in range(1, n))*mp.power(n, -a)
         for n in range(2, 8)}
    Q = (p[7]*p[2]**3-3*p[6]*p[3]*p[2]**2
         +3*p[5]*p[3]**2*p[2]-p[4]*p[3]**3)/(2*p[2]**4)
    return a, Q


def main():
    mp.mp.dps = 100
    lo, hi = mp.mpf(".99"), mp.mpf(".999")
    assert threshold_and_quartic(lo)[1] < 0 < threshold_and_quartic(hi)[1]
    for _ in range(250):
        mid = (lo+hi)/2
        if threshold_and_quartic(mid)[1] > 0:
            hi = mid
        else:
            lo = mid
    b = (lo+hi)/2
    a, Q = threshold_and_quartic(b)
    data = {
        "status": "Floating-point diagnostic; not an interval certificate or a uniqueness proof.",
        "arithmetic": "mpmath at 100 decimal digits",
        "method": "250 bisections within b in (.99,.999), along the unique local K-threshold; only p_n for n<=7",
        "b_quartic_zero": mp.nstr(b, 70),
        "a_star_at_quartic_zero": mp.nstr(a, 70),
        "absolute_Q_residual": mp.nstr(abs(Q), 12),
        "scope": "One sign-change point is suggested. No claim of uniqueness or absence of additional sign changes."
    }
    path = Path(__file__).resolve().parents[2] / "data" / "kernels" / "quartic_sign_transition_diagnostic.json"
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(data))


if __name__ == "__main__":
    main()
