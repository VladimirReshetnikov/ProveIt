#!/usr/bin/env python3
"""High-precision diagnostic checks for analytic Barnes-G identities.

This file uses mpmath floating-point arithmetic and is intentionally labelled
DIAGNOSTIC.  It is useful for catching transcription errors, but is not a
formal proof or a certified interval calculation.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import mpmath as mp


def relerr(a, b):
    return abs(a-b) / max(mp.mpf(1), abs(a), abs(b))


def cl2(theta):
    # Im Li_2(e^{i theta}); stable away from the branch endpoint in our tests.
    return mp.im(mp.polylog(2, mp.e ** (1j * theta)))


def A_const():
    return mp.e ** (mp.mpf(1)/12 - mp.diff(lambda s: mp.zeta(s), -1))


def K_mult(n):
    A = A_const()
    return (A * mp.e ** (-mp.mpf(1)/12)) ** (n*n-1) * n ** (mp.mpf(5)/12) * (2*mp.pi) ** (mp.mpf(n-1)/2)


def multiplication_rhs(n, z):
    p = mp.mpf(1)
    for i in range(n):
        for j in range(n):
            p *= mp.barnesg(z + mp.mpf(i+j)/n)
    return (K_mult(n) * n ** (mp.mpf(n*n)*z*z/2 - n*z)
            * (2*mp.pi) ** (-(mp.mpf(n*n-n)/2)*z) * p)


def run(dps: int) -> dict:
    mp.mp.dps = dps
    A = A_const()
    cat = mp.catalan
    records = []

    # Functional equation and finite product.
    for z in [mp.mpf('0.37'), mp.mpf('1.2')+mp.mpf('0.4')*1j,
              mp.mpf('2.75')-mp.mpf('0.2')*1j]:
        lhs = mp.barnesg(z+1)
        rhs = mp.gamma(z)*mp.barnesg(z)
        records.append(("functional", str(z), relerr(lhs, rhs)))

    for k, n in [(mp.mpf('0.7'), 4), (mp.mpf('1.2')+0.2j, 3)]:
        lhs = mp.fprod([mp.gamma(k+i) for i in range(1, n+1)])
        rhs = mp.barnesg(k+n+1)/mp.barnesg(k+1)
        records.append(("finite_product", f"k={k},n={n}", relerr(lhs, rhs)))

    # Derivative and reflection.
    c = mp.log(2*mp.pi)/2 + mp.mpf('0.5')
    for z in [mp.mpf('0.8'), mp.mpf('1.3')+0.15j]:
        lhs = mp.diff(mp.barnesg, z)
        rhs = mp.barnesg(z)*((z-1)*mp.digamma(z)-z+c)
        records.append(("derivative", str(z), relerr(lhs, rhs)))

    for z in [mp.mpf('0.2'), mp.mpf('0.37')]:
        lhs = mp.log(mp.barnesg(1-z)/mp.barnesg(1+z))
        rhs = mp.quad(lambda x: mp.pi*x/mp.tan(mp.pi*x), [0,z]) - z*mp.log(2*mp.pi)
        records.append(("kinkelin_reflection", str(z), relerr(lhs, rhs)))
        rhs2 = z*mp.log(mp.sin(mp.pi*z)/mp.pi)+cl2(2*mp.pi*z)/(2*mp.pi)
        records.append(("clausen_reflection", str(z), relerr(lhs, rhs2)))

    # Multiplication formula, including duplication.
    for n, z in [(2, mp.mpf('0.71')), (3, mp.mpf('0.83')+0.12j), (4, mp.mpf('1.11'))]:
        lhs = mp.barnesg(n*z)
        rhs = multiplication_rhs(n, z)
        records.append(("multiplication", f"n={n},z={z}", relerr(lhs, rhs)))

    # Special values.
    specials = {
        "G(1/2)": (mp.barnesg(mp.mpf(1)/2), A**(-mp.mpf(3)/2)*mp.pi**(-mp.mpf(1)/4)*mp.e**(mp.mpf(1)/8)*2**(mp.mpf(1)/24)),
        "G(3/2)": (mp.barnesg(mp.mpf(3)/2), A**(-mp.mpf(3)/2)*mp.pi**(mp.mpf(1)/4)*mp.e**(mp.mpf(1)/8)*2**(mp.mpf(1)/24)),
        "G(5/2)": (mp.barnesg(mp.mpf(5)/2), A**(-mp.mpf(3)/2)*mp.pi**(mp.mpf(3)/4)*mp.e**(mp.mpf(1)/8)*2**(-mp.mpf(23)/24)),
        "G(1/4)": (mp.barnesg(mp.mpf(1)/4), A**(-mp.mpf(9)/8)*mp.gamma(mp.mpf(1)/4)**(-mp.mpf(3)/4)*mp.e**(mp.mpf(3)/32-cat/(4*mp.pi))),
        "G(3/4)": (mp.barnesg(mp.mpf(3)/4), A**(-mp.mpf(9)/8)*mp.gamma(mp.mpf(3)/4)**(-mp.mpf(1)/4)*mp.e**(mp.mpf(3)/32+cat/(4*mp.pi))),
    }
    for name,(lhs,rhs) in specials.items():
        records.append(("special_value", name, relerr(lhs,rhs)))

    # Corrected characterization: Gamma(n)^x, not Gamma(x)^n.
    for x in [mp.mpf('0.3'), mp.mpf('1.0'), mp.mpf('1.7')]:
        for n in [20, 80]:
            ratio = mp.barnesg(x+n)/(mp.gamma(n)**x * n**(x*(x-1)/2)*mp.barnesg(n))
            records.append(("corrected_asymptotic_ratio", f"x={x},n={n}", abs(ratio-1)))

    identity_errors = [e for fam,_,e in records if fam != 'corrected_asymptotic_ratio']
    asym = [e for fam,_,e in records if fam == 'corrected_asymptotic_ratio']
    maxerr = max(identity_errors)
    # For x=0.3 and 1.7 the n=80 residual must improve on n=20; x=1 is exact.
    asym_ok = asym[1] < asym[0] and asym[3] == 0 and asym[2] == 0 and asym[5] < asym[4]
    return {
        "checker": "check_numeric_identities.py",
        "status": "diagnostic floating-point checks; not a proof",
        "mpmath_dps": dps,
        "records": [{"family":a,"case":b,"error":mp.nstr(e,18)} for a,b,e in records],
        "max_identity_error": mp.nstr(maxerr,18),
        "identity_checks_below_1e-50": bool(maxerr < mp.mpf('1e-50')),
        "asymptotic_residuals_decrease": bool(asym_ok),
        "all_ok": bool(maxerr < mp.mpf('1e-50') and asym_ok),
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--dps',type=int,default=90)
    ap.add_argument('--output',type=Path)
    ns=ap.parse_args()
    out=run(ns.dps)
    text=json.dumps(out,indent=2,sort_keys=True)+"\n"
    if ns.output:
        ns.output.parent.mkdir(parents=True,exist_ok=True)
        ns.output.write_text(text,encoding='utf-8')
    print(text,end='')
    raise SystemExit(0 if out['all_ok'] else 1)

if __name__=='__main__':
    main()
