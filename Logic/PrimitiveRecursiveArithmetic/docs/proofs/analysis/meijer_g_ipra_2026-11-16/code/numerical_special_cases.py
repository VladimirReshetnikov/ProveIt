#!/usr/bin/env python3
"""High-precision numerical regression checks for selected Meijer-G identities.

The script uses mpmath's independent Meijer-G implementation.  It is validation
only: numerical samples do not prove universal identities or iPRA theorems.
"""
from __future__ import annotations

import json
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "evidence" / "numerical_special_cases.json"
mp.mp.dps = 80


def G(an, ap, bm, bq, z, r=1):
    return mp.meijerg([an, ap], [bm, bq], z, r=r)


def encode(x):
    z = mp.mpc(x)
    if abs(z.imag) < mp.mpf("1e-70"):
        return mp.nstr(z.real, 60)
    return {"re": mp.nstr(z.real, 60), "im": mp.nstr(z.imag, 60)}


def add_case(records, name, lhs, rhs, parameters, tolerance=mp.mpf("1e-55")):
    err = abs(lhs-rhs)
    scale = max(mp.mpf(1), abs(lhs), abs(rhs))
    rel = err/scale
    ok = rel < tolerance
    records.append({
        "name": name,
        "parameters": {k: encode(v) for k,v in parameters.items()},
        "lhs": encode(lhs),
        "rhs": encode(rhs),
        "absolute_error": mp.nstr(err, 20),
        "relative_error": mp.nstr(rel, 20),
        "tolerance": mp.nstr(tolerance, 5),
        "ok": bool(ok),
    })
    if not ok:
        raise AssertionError(f"{name} failed: rel={rel}")


def six_term_bracket(x):
    z = x*x
    return (
        3/(4*mp.pi)*G([], [mp.mpf("1.5")], [mp.mpf("-0.5"), 0, 1], [], z)
        +3/(8*mp.pi*x*x)*G([], [mp.mpf("2.5")], [0, mp.mpf("0.5"), 2], [], z)
        +mp.pi/4*G([], [mp.mpf("-0.5"), mp.mpf("0.5")],
                     [-1, 0], [mp.mpf("-0.5"), mp.mpf("-0.5")], z)
        -mp.pi/2*G([], [mp.mpf("-0.5"), mp.mpf("0.5")],
                     [-1, 1], [mp.mpf("-0.5"), mp.mpf("-0.5")], z)
        +mp.pi/8*G([], [mp.mpf("-0.5"), mp.mpf("1.5")],
                     [0, 0], [mp.mpf("-0.5"), mp.mpf("-0.5")], z)
        -mp.pi/4*G([], [mp.mpf("-0.5"), mp.mpf("1.5")],
                     [0, 1], [mp.mpf("-0.5"), mp.mpf("-0.5")], z)
    )


def main():
    rec = []
    for x in map(mp.mpf, ["0.3", "1.2", "2.0"]):
        add_case(rec, "exp", G([], [], [0], [], -x), mp.e**x, {"x": x})
        add_case(rec, "cos", mp.sqrt(mp.pi)*G([], [], [0], [mp.mpf("0.5")], x*x/4),
                 mp.cos(x), {"x": x})
        add_case(rec, "sin", mp.sqrt(mp.pi)*G([], [], [mp.mpf("0.5")], [0], x*x/4),
                 mp.sin(x), {"x": x})
        add_case(rec, "log1p", G([1,1], [], [1], [0], x), mp.log(1+x), {"x": x})
        add_case(rec, "rational", G([1,1], [], [1], [1], x), x/(1+x), {"x": x})
        add_case(rec, "arctan", mp.mpf("0.5")*G([mp.mpf("0.5"),1], [],
                 [mp.mpf("0.5")], [0], x*x), mp.atan(x), {"x": x})

    for alpha in map(mp.mpf, ["0.7", "2.3"]):
        for x in map(mp.mpf, ["0.4", "1.6"]):
            add_case(rec, "lower_incomplete_gamma",
                     G([1], [], [alpha], [0], x), mp.gammainc(alpha, 0, x),
                     {"alpha": alpha, "x": x})
            add_case(rec, "upper_incomplete_gamma",
                     G([], [1], [alpha,0], [], x), mp.gammainc(alpha, x, mp.inf),
                     {"alpha": alpha, "x": x})

    for nu in map(mp.mpf, ["0.3", "1.2"]):
        for x in map(mp.mpf, ["0.7", "2.0"]):
            add_case(rec, "bessel_J", G([], [], [nu/2], [-nu/2], x*x/4),
                     mp.besselj(nu,x), {"nu":nu,"x":x})
            add_case(rec, "bessel_Y", G([], [-(nu+1)/2], [nu/2,-nu/2],
                     [-(nu+1)/2], x*x/4), mp.bessely(nu,x), {"nu":nu,"x":x})
            add_case(rec, "bessel_I", mp.power(1j,-nu)*G([], [], [nu/2],[-nu/2],-x*x/4),
                     mp.besseli(nu,x), {"nu":nu,"x":x})
            add_case(rec, "bessel_K", mp.mpf("0.5")*G([], [], [nu/2,-nu/2],[],x*x/4),
                     mp.besselk(nu,x), {"nu":nu,"x":x})

    a = mp.mpf("1.3"); x = mp.mpf("0.4")
    for n in range(4):
        add_case(rec, "lerch_positive",
                 G([0]+[1-a]*n, [], [0], [-a]*n, -x), mp.lerchphi(x,n,a),
                 {"a":a,"x":x,"n":n})
        add_case(rec, "lerch_negative",
                 G([0]+[-a]*n, [], [0], [1-a]*n, -x), mp.lerchphi(x,-n,a),
                 {"a":a,"x":x,"n":n})

    z = mp.mpf("0.7")
    add_case(rec, "generalized_r_cos",
             G([], [], [0], [mp.mpf("0.5")], z/2, r=mp.mpf("0.5")),
             mp.cos(z)/mp.sqrt(mp.pi), {"z":z,"r":mp.mpf("0.5")})
    a = mp.mpf("0.8"); z = mp.mpf("2.2")
    add_case(rec, "reciprocal_exponential", G([1-a],[],[],[],z),
             z**(-a)*mp.e**(-1/z), {"a":a,"z":z})

    for x in map(mp.mpf, ["0.5","0.7","1.0","1.3","2.0"]):
        add_case(rec, "six_term_identity_positive", six_term_bracket(x), x, {"x":x},
                 tolerance=mp.mpf("1e-45"))

    # Whittaker specialization of the generalized Laplace kernels.
    for m, k, x in [
        (mp.mpf("0.7"), mp.mpf("0.2"), mp.mpf("0.8")),
        (mp.mpf("1.1"), mp.mpf("-0.3"), mp.mpf("1.4")),
        (mp.mpf("0.4"), mp.mpf("0.1"), mp.mpf("2.1")),
    ]:
        add_case(
            rec, "whittaker_forward_kernel",
            G([], [m-k], [0, 2*m], [], x),
            x**(m-mp.mpf("0.5"))*mp.e**(-x/2)*mp.whitw(k+mp.mpf("0.5"), m, x),
            {"m":m, "k":k, "x":x},
        )
        add_case(
            rec, "whittaker_inverse_kernel",
            x**(m+k)*G([k-m], [], [0], [-2*m], -x),
            (mp.gamma(1+m-k)/mp.gamma(1+2*m))
            *x**(k-mp.mpf("0.5"))*mp.e**(x/2)*mp.whitm(k-mp.mpf("0.5"), m, x),
            {"m":m, "k":k, "x":x},
        )

    summary = {
        "mpmath_version": mp.__version__,
        "decimal_precision": mp.mp.dps,
        "checks": len(rec),
        "all_passed": all(r["ok"] for r in rec),
        "max_relative_error": mp.nstr(max(mp.mpf(r["relative_error"]) for r in rec), 20),
        "records": rec,
        "warning": "Numerical samples are regression evidence, not proofs."
    }
    OUT.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"wrote {OUT}")
    print(f"{summary['checks']} high-precision numerical checks passed")


if __name__ == "__main__":
    main()
