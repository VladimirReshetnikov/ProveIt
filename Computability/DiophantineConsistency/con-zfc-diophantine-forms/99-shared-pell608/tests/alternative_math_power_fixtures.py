#!/usr/bin/env python3
"""Independent canonical witness checks for the reduced positive power macro.

No builder imports. This is finite implementation evidence; the universal
existence proof is in alternative_math_power_review.md.
"""
from __future__ import annotations

from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def require(condition, label):
    if not condition:
        raise ValueError(label)


def pell(a: int, j: int) -> tuple[int, int]:
    require(a >= 2 and j >= 0, "Pell input range")
    if j == 0:
        return 1, 0
    x, y = pell(a, j // 2)
    xx, yy = 2 * x * x - 1, 2 * x * y
    if j % 2:
        return a * xx + (a * a - 1) * yy, xx + a * yy
    return xx, yy


def exact_quotient(numerator: int, denominator: int, label: str) -> int:
    require(denominator > 0, label + ": positive denominator")
    q, r = divmod(numerator, denominator)
    require(r == 0 and q >= 0, label + ": nonnegative integral quotient")
    return q


def certificate(n: int, k: int) -> dict[str, int]:
    require(n >= 1 and k >= 1, "positive power inputs")
    m, w = n**k, n + k
    a, wz = pell(w + 1, w)
    z = exact_quotient(wz, w, "majorant Z")
    t = 2 * a * n - n * n - 1
    x, y = pell(a, k)
    index = 2 * k * y
    u, v = pell(a, index)
    four_y = 4 * y
    require(gcd(u, four_y) == 1, "CRT coprimality")
    qb = ((1 - a) * pow(u, -1, four_y)) % four_y
    b = a + u * qb
    s, r = pell(b, k)
    return dict(n=n, k=k, m=m, W=w, A=a, Z=z, T=t, X=x, Y=y,
                U=u, V=v, B=b, S=s, R=r, index=index,
                qB=qb, qS=exact_quotient(s-x, u, "S quotient"),
                qR=exact_quotient(r-k, four_y, "R quotient"),
                qP=exact_quotient(x+y*n-y*a-m, t, "power quotient"),
                q4=exact_quotient(b-1, four_y, "B quotient")-1,
                vd=exact_quotient(v, y*y, "V quotient")-1,
                yk=y-k, gap=t-m-1)


def check(c: dict[str, int]) -> dict:
    require(all(value >= 0 for value in c.values()), "all witnesses natural")
    n,k,m,w,a,z,t,x,y,u,v,b,s,r = [c[v] for v in
        ("n","k","m","W","A","Z","T","X","Y","U","V","B","S","R")]
    residuals = {
        "majorant": w-n-k,
        "norm1": x*x+y*y-(a*y)**2-1,
        "norm2": u*u+v*v-(a*v)**2-1,
        "norm3": s*s+r*r-(b*r)**2-1,
        "last_norm": a*a+(w*z)**2-((w+1)*w*z)**2-1,
        "B_orientation": b-a-u*c["qB"],
        "S_orientation": s-x-u*c["qS"],
        "R_orientation": r-k-4*y*c["qR"],
        "power_orientation": x+y*n-y*a-m-t*c["qP"],
        "B_positive_quotient": b-1-4*y*(c["q4"]+1),
        "V_positive_multiple": v-y*y*(c["vd"]+1),
        "T_definition": 2*a*n-t-n*n-1,
        "Y_alias": y-k-c["yk"],
        "T_alias": t-m-c["gap"]-1,
        "power_output": m-n**k,
    }
    require(all(v == 0 for v in residuals.values()), "all defining rows vanish")
    require(a >= 2 and b >= 2 and y >= k and 0 < m < t, "derived ranges")
    require(u > a and b >= a and s >= x and r >= k, "oriented bounds")
    previous_y = pell(a, k-1)[1]
    require(x-a*y == -previous_y, "backward Pell identity")
    require(n*y-previous_y > 0, "positive power-congruence difference")

    # Exact corruption controls: a wrong output must fail the quotient row
    # and a wrong canonical Pell ordinate must fail its one-product norm.
    require(x+y*n-y*a-(m+1)-t*c["qP"] != 0, "output corruption detected")
    require(x*x+(y+1)**2-(a*(y+1))**2-1 != 0,
            "Pell ordinate corruption detected")

    encoded = json.dumps(c, sort_keys=True, separators=(",", ":")).encode()
    return {"n": n, "k": k, "output": m, "W": w, "A": a,
            "U_bit_length": u.bit_length(), "S_bit_length": s.bit_length(),
            "largest_decimal_digits": max(len(str(v)) for v in c.values()),
            "zero_residuals": len(residuals), "negative_controls": 2,
            "witness_sha256": sha256(encoded).hexdigest(), "passed": True}


if __name__ == "__main__":
    fixtures = [check(certificate(n,k)) for n,k in [(1,1),(2,1),(1,2)]]
    receipt = {"scope": "Finite canonical power certificates only; universal proof separate",
               "builder_imported": False, "fixtures": fixtures, "passed": True}
    destination = Path(__file__).with_name("alternative_math_power_fixture_results.json")
    destination.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
