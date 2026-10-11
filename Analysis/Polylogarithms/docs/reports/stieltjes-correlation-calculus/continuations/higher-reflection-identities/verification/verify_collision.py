"""Independent symbolic identities and direct finite-part quadrature.

The numerical integrator does not use the local collision counterterm to
evaluate the separated integral.  It subtracts each actual right pole in
the original circle integral, then adds its elementary finite primitive.
"""

import itertools
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_checks():
    e = sp.Symbol("e", positive=True)
    g, z2, z3, z4 = sp.symbols("g z2 z3 z4")

    def h(t):
        return g - z2*t + z3*t**2 - z4*t**3

    def counterterm(shifts):
        ans = 0
        for k in range(2, len(shifts)+1):
            for ss in itertools.combinations(range(len(shifts)), k):
                for i in ss[1:]:
                    num = sp.prod(h(shifts[j]-shifts[i])
                                  for j in range(len(shifts)) if j not in ss)
                    den = sp.prod(shifts[j]-shifts[i] for j in ss if j != i)
                    ans -= num/den * sp.log(shifts[i]-shifts[ss[0]])
        return ans

    result = {}
    th = counterterm([0, e, e+e**2])
    actual = sp.series(sp.expand_log(th, force=True), e, 0, 1).removeO().expand()
    expected = (((1+2*g)*sp.log(e)-1)/e**2
                + ((2*g+2*z2-1)*sp.log(e)+sp.Rational(3, 2))/e
                + (1-g+2*z2+2*z3)*sp.log(e)+g-sp.Rational(11, 6))
    assert sp.simplify(actual-expected) == 0
    result["hierarchical_cubic_full_expansion"] = str(expected)

    tq = counterterm([0, e, 2*e, 3*e])
    actual = sp.series(sp.expand_log(tq, force=True), e, 0, 1).removeO().expand()
    constant = actual.coeff(e, 0).subs(sp.log(e), 0).expand()
    expected = g*z2*(2*sp.log(2)+sp.log(3)) - sp.Rational(3, 2)*z3*(3*sp.log(2)+sp.log(3))
    assert sp.simplify(constant-expected) == 0
    result["equally_spaced_quartic_constant"] = str(expected)
    return result


def f(x):
    return -mp.digamma(x)


def h(x):
    return -mp.digamma(1+x)


def separated_fp(shifts):
    """Integrate each actual circle interval by independent pole subtraction."""
    shifts = list(map(mp.mpf, shifts))
    d = len(shifts)
    ordered = sorted(range(d), key=lambda i: (-shifts[i]) % 1)
    locations = [(-shifts[i]) % 1 for i in ordered]
    ans = mp.mpf(0)
    for index, i in enumerate(ordered):
        ell = (locations[index+1] if index+1 < d else locations[0]+1)-locations[index]
        offsets = [(shifts[j]-shifts[i]) % 1 for j in range(d) if j != i]
        v0 = [f(u) for u in offsets]
        residue = mp.fprod(v0)
        deriv = sum(-mp.polygamma(1, offsets[j]) * mp.fprod(v0[:j]+v0[j+1:])
                    for j in range(d-1))
        cutoff = min(offsets) * mp.sqrt(mp.eps)

        def integrand(t):
            if abs(t) < cutoff:
                return deriv + mp.euler*residue
            vals = [f(u+t) for u in offsets]
            prod = mp.fprod(vals)
            # Telescoping product difference improves stability at a short gap.
            diff = sum((vals[j]-v0[j]) * mp.fprod(vals[:j]) * mp.fprod(v0[j+1:])
                       for j in range(d-1))
            return diff/t + h(t)*prod

        ans += mp.quad(integrand, [0, ell/4, ell/2, ell]) + residue*mp.log(ell)
    return ans


def local_counterterm(shifts):
    shifts = list(map(mp.mpf, shifts))
    ans = mp.mpf(0)
    d = len(shifts)
    for k in range(2, d+1):
        for ss in itertools.combinations(range(d), k):
            m = min(ss, key=lambda i: shifts[i])
            for i in ss:
                if i == m:
                    continue
                num = mp.fprod(h(shifts[j]-shifts[i]) for j in range(d) if j not in ss)
                den = mp.fprod(shifts[j]-shifts[i] for j in ss if j != i)
                ans -= num/den*mp.log(shifts[i]-shifts[m])
    return ans


def merged_fp(d):
    """Direct endpoint Laurent subtraction for the merged moment."""
    count = mp.mp.dps + 20
    base = [mp.mpf(1), mp.euler] + [(-1)**(n-1)*mp.zeta(n) for n in range(2, count)]
    coeff = [mp.mpf(1)]
    for _ in range(d):
        prod = [mp.mpf(0)]*count
        for i, a in enumerate(coeff):
            for j, b in enumerate(base[:count-i]):
                prod[i+j] += a*b
        coeff = prod

    def regular(x):
        if x < mp.mpf("0.1"):
            return mp.polyval(list(reversed(coeff[d:])), x)
        return f(x)**d - mp.fsum(coeff[k]*x**(k-d) for k in range(d))

    return (mp.quad(regular, [0, mp.mpf("0.1"), mp.mpf("0.5"), 1])
            + mp.fsum(coeff[k]/(k-d+1) for k in range(d-1)))


def main():
    mp.mp.dps = 55
    report = {"symbolic": symbolic_checks(), "working_decimal_digits": mp.mp.dps,
              "quadrature": []}
    for d in (3, 4):
        q = merged_fp(d)
        print("Q", d, mp.nstr(q, 32), flush=True)
        report[f"Q_{d}"] = mp.nstr(q, 50)
        for es in ("0.03", "0.01", "0.003", "0.001"):
            e = mp.mpf(es)
            shifts = [mp.mpf(0), e, e+e**2] if d == 3 else [i*e for i in range(4)]
            c = separated_fp(shifts)
            t = local_counterterm(shifts)
            error = c-t-q
            row = {"d": d, "epsilon": es, "C_minus_T": mp.nstr(c-t, 40),
                   "C_minus_T_minus_Q": mp.nstr(error, 30)}
            report["quadrature"].append(row)
            print(json.dumps(row), flush=True)
    path = Path(__file__).with_name("collision_verification.json")
    path.write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
