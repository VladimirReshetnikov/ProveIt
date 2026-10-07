#!/usr/bin/env python3
"""Optional high-precision diagnostics for Report230 (requires mpmath).

No transcendental result here is an interval certificate or finite-n error
bound. 'finite' evaluates the complete original integer and transformed sums.
'marked' uses an explicitly reported central window and analytic tail bounds.
'inverse' performs a specified finite number of Newton steps on a finite smooth
model. It does not certify threshold rounding for arbitrary y.
"""
from __future__ import annotations

import argparse
import json
from math import ceil

from endpoint import (MAX_CRITICAL_ORDER, MAX_EXACT_N, MAX_ORDER, MAX_P,
                      _integer, coefficient_arrays, critical_coefficients,
                      exact_count, fractional_coefficients)

WARNING_P3 = ("At p=3,n=10000, fractional truncation through t^12 can still have "
              "about -66% relative error, while the full H order 12 has about "
              "+0.12% error. Formal order does not guarantee moderate-n accuracy. "
              "Run suite --deep to reproduce this warning.")


def _mpmath():
    try:
        import mpmath
    except ImportError as exc:
        raise RuntimeError("diagnostics require optional mpmath; the exact core and selftests do not") from exc
    return mpmath


def _precision(dps):
    _integer("dps", dps, 30, 200)


def _mpf(mp, f):
    return mp.mpf(f.numerator)/f.denominator


def _evaluate(mp, poly, x):
    return mp.fsum(_mpf(mp, a)*x**d for d, a in sorted(poly.items()))


def _parameters(mp, p, n):
    q = p+1
    beta = mp.mpf(1)/q
    c = mp.exp(mp.mpf(p*p)/q)*mp.power(q, -beta)
    lam = c*mp.power(n, beta)
    offset = 3*mp.e/8 if p == 1 else mp.mpf(0)
    return q, beta, c, lam, offset


def _delta(mp, p, n, r):
    q = p+1
    m = (n+p*r)//q
    # For allowed r, m-r=(n-r)/q is a nonnegative integer. This log-gamma
    # representation evaluates the exact falling factorial, with no Taylor or
    # asymptotic coefficients. At r=0 it also avoids any 0*log(0) ambiguity.
    if r == 0:
        return mp.mpf(0)
    return (mp.mpf(p*n+r)/q*mp.log1p(mp.mpf(p*r)/n)-mp.mpf(p*p*r)/q
            +mp.loggamma(m+1)-mp.loggamma(m-r+1)-r*mp.log(m))


def finite_sum_diagnostic(p, n, order=8, h_order=8, dps=80):
    """Compare COMPLETE integer/transformed sums and two different truncations."""
    _integer("p", p, 1, MAX_P)
    _integer("n", n, 1, MAX_EXACT_N)
    _integer("h_order", h_order, 0, MAX_ORDER)
    _precision(dps)
    C = critical_coefficients(order) if p == 1 else fractional_coefficients(p, order)
    U = coefficient_arrays(p, h_order)[2] if p >= 2 else None
    mp = _mpmath()
    with mp.workdps(dps):
        q, beta, c, lam, offset = _parameters(mp, p, n)
        a = exact_count(p, n)
        logB = mp.mpf(p*n)/q*mp.log(mp.mpf(n)/q)
        norm = q*mp.exp(mp.log(a)-logB-lam+offset)
        loglam = mp.log(lam)
        transformed = q*mp.exp(offset)*mp.fsum(
            mp.exp(-lam+r*loglam-mp.loggamma(r+1)+_delta(mp, p, n, r))
            for r in range(n % q, n+1, q))
        t = mp.power(n, -beta)
        fractional = mp.fsum(_evaluate(mp, poly, c)*t**k for k, poly in enumerate(C))
        text = lambda x: mp.nstr(x, min(40, dps-10))
        out = {"p": p, "n": n, "dps": dps,
               "integer_bit_length": a.bit_length(),
               "complete_transformed_terms": (n-n % q)//q+1,
               "lambda": text(lam), "normalized_integer": text(norm),
               "normalized_transformed": text(transformed),
               "identity_relative_discrepancy": text(abs(transformed/norm-1)),
               "fractional_order": order,
               "fractional_value": text(fractional),
               "fractional_relative_error": text(fractional/norm-1),
               "normalization": "critical M1" if p == 1 else "subcritical M_p",
               "certified_interval": False}
        if U is not None:
            full_h = mp.fsum(_evaluate(mp, u, lam)/mp.mpf(n)**j for j, u in enumerate(U))
            out.update(full_H_order=h_order, full_H_value=text(full_h),
                       full_H_relative_error=text(full_h/norm-1))
        if p == 3:
            out["preasymptotic_warning"] = WARNING_P3
        return out


def _poisson_tail_bound(mp, nu, lo, hi):
    """Chernoff bound for P(X<lo or X>hi), X~Pois(nu), with integer cutoffs."""
    bound = mp.mpf(0)
    if lo > 0:
        a = mp.mpf(lo-1)
        if a >= nu:
            bound += 1
        elif a == 0:
            bound += mp.exp(-nu)
        else:
            bound += mp.exp(-nu+a*(1+mp.log(nu/a)))
    a = mp.mpf(hi+1)
    if a <= nu:
        bound += 1
    else:
        bound += mp.exp(-nu+a*(1+mp.log(nu/a)))
    return min(mp.mpf(1), bound)


def _residue_probability(mp, nu, a, q):
    return mp.re(mp.fsum(mp.exp(nu*(mp.exp(2j*mp.pi*j/q)-1))
                        *mp.exp(-2j*mp.pi*j*a/q) for j in range(q))/q)


def marked_diagnostic(p, n, dps=80):
    """Window-based mean/variance/TV diagnostics; explicit omitted-tail bounds.

    Each window law is normalized on that window. TV error versus the true
    complete laws is bounded by the sum of their omitted-tail probabilities,
    using the displayed Chernoff bounds (evaluated non-rigorously by mpmath).
    Bounds here control TV only, not the numerical moment truncation error.
    """
    _integer("p", p, 2, 8)
    _integer("n", n, 1000, 10**12)
    _precision(dps)
    mp = _mpmath()
    with mp.workdps(dps):
        q, _, _, lam, _ = _parameters(mp, p, n)
        A = (mp.mpf(p*p)+mp.mpf(1)/q)/2
        b = A-mp.mpf(q)/2
        mu = n/(2*A)*mp.lambertw(2*A*lam/n*mp.exp(-b/n))
        lo = max(0, int(mp.floor(min(lam, mu)-18*mp.sqrt(lam)-50)))
        hi = min(n, int(mp.ceil(max(lam, mu)+18*mp.sqrt(lam)+50)))
        lo += (n-lo) % q
        terms = max(0, (hi-lo)//q+1)
        if terms < 1 or terms > 100000:
            raise ValueError("marked window must contain between 1 and 100000 lattice points")
        if not (lo <= mu <= hi and lo <= lam <= hi):
            raise ValueError("n is outside the diagnostic's central-window regime; increase n or decrease p")
        rs = range(lo, hi+1, q)
        true, original, tilted = [], [], []
        for r in rs:
            logfac = mp.loggamma(r+1)
            lp = -lam+r*mp.log(lam)-logfac
            true.append(mp.exp(lp+_delta(mp, p, n, r)))
            original.append(mp.exp(lp))
            tilted.append(mp.exp(-mu+r*mp.log(mu)-logfac))
        ztrue, zorig, ztilt = map(mp.fsum, (true, original, tilted))
        true = [v/ztrue for v in true]
        original = [v/zorig for v in original]
        tilted = [v/ztilt for v in tilted]
        mean = mp.fsum(r*v for r, v in zip(rs, true))
        variance = mp.fsum((r-mean)**2*v for r, v in zip(rs, true))
        tv0 = mp.fsum(abs(v-w) for v, w in zip(true, original))/2
        tv1 = mp.fsum(abs(v-w) for v, w in zip(true, tilted))/2
        tail0 = _poisson_tail_bound(mp, lam, lo, hi)
        tail1 = _poisson_tail_bound(mp, mu, lo, hi)
        ref0 = tail0/_residue_probability(mp, lam, n % q, q)
        ref1 = tail1/_residue_probability(mp, mu, n % q, q)
        exact_tail = tail0/ztrue  # Delta<=0; full exact normalizer >= ztrue
        predmean = lam-(2*A*lam**2+b*lam)/n
        predvar = lam-(4*A*lam**2+b*lam)/n
        text = lambda x: mp.nstr(x, min(30, dps-10))
        return {"p": p, "n": n, "dps": dps,
                "lambda": text(lam), "mu": text(mu),
                "window": [lo, hi], "window_lattice_points": terms,
                "mean_window": text(mean), "variance_window": text(variance),
                "mean_first_order_residual_over_lambda3_n2": text((mean-predmean)*n*n/lam**3),
                "variance_first_order_residual_over_lambda3_n2": text((variance-predvar)*n*n/lam**3),
                "tv_original_window": text(tv0), "tv_tilted_window": text(tv1),
                "tv_original_over_equivalent": text(tv0/(A*mp.sqrt(2/mp.pi)*lam**mp.mpf('1.5')/n)),
                "tv_tilted_over_equivalent": text(tv1/(A*mp.sqrt(2/(mp.pi*mp.e))*mu/n)),
                "tv_original_absolute_truncation_bound": text(min(1, exact_tail+ref0)),
                "tv_tilted_absolute_truncation_bound": text(min(1, exact_tail+ref1)),
                "reference": "Poisson conditioned on r congruent n mod (p+1)",
                "moment_truncation": "central-window diagnostics; TV tail bounds do not bound moment errors",
                "certified_interval": False}


def newton_diagnostic(p, n, order=4, steps=3, dps=80, exact_target=False):
    """Test finite smooth-model Newton inversion at model or exact-count target.

    Default target Y=F_K(n) has known model root n. With exact_target=True the
    target is log a_p(n), so residual index errors also include model truncation.
    Positivity, finite values, and an increasing local model are checked at every
    step. Convexity and a global finite-n onset are not certified by these checks.
    """
    _integer("p", p, 1, MAX_P)
    _integer("n", n, 1, MAX_EXACT_N if exact_target else 10**12)
    _integer("steps", steps, 0, 12)
    if type(exact_target) is not bool:
        raise TypeError("exact_target must be bool")
    _precision(dps)
    polys = critical_coefficients(order) if p == 1 else fractional_coefficients(p, order)
    mp = _mpmath()
    with mp.workdps(dps):
        q, beta, c, _, offset = _parameters(mp, p, n)
        kap = mp.mpf(p)/q
        coeffs = [_evaluate(mp, poly, c) for poly in polys]
        def evaluate(x):
            if not mp.isfinite(x) or x <= 0:
                raise ValueError("Newton iterate left the positive finite domain")
            Q = mp.fsum(a*x**(-beta*j) for j, a in enumerate(coeffs))
            if not mp.isfinite(Q) or Q <= 0:
                raise ValueError("finite Q_K is not positive; increase n or change order")
            Qp = mp.fsum(-beta*j*a*x**(-beta*j-1) for j, a in enumerate(coeffs) if j)
            F = kap*x*mp.log(x/q)+c*x**beta-mp.log(q)-offset+mp.log(Q)
            Fp = kap*(mp.log(x/q)+1)+c*beta*x**(beta-1)+Qp/Q
            if not mp.isfinite(F) or not mp.isfinite(Fp) or Fp <= 0:
                raise ValueError("finite model is not increasing at this Newton iterate")
            return F, Fp
        Y = mp.log(exact_count(p, n)) if exact_target else evaluate(mp.mpf(n))[0]
        Z = Y+mp.log(q)+offset
        if Z <= 0:
            raise ValueError("Lambert core requires a positive target offset")
        x = q*Z/(p*mp.lambertw(Z/p))
        xs = [x]
        for _ in range(steps):
            value, derivative = evaluate(x)
            x -= (value-Y)/derivative
            evaluate(x)
            xs.append(x)
        text = lambda v: mp.nstr(v, min(40, dps-10))
        return {"p": p, "n": n, "order": order, "steps": steps, "dps": dps,
                "target": "log exact a_p(n)" if exact_target else "finite model F_K(n)",
                "iterates": [text(v) for v in xs],
                "index_errors": [text(v-n) for v in xs],
                "final_model_residual": text(evaluate(x)[0]-Y),
                "certified_threshold_rounding": False,
                "qualification": "nearest-integer recovery is asymptotic and needs an exact-range input; arbitrary thresholds require a ceiling envelope"}


def _main():
    parser = argparse.ArgumentParser(description=__doc__, epilog=WARNING_P3,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    s = sub.add_parser("finite", help="complete exact integer and transformed sums")
    s.add_argument("--p", type=int, default=2)
    s.add_argument("--n", type=int, default=300)
    s.add_argument("--order", type=int, default=8)
    s.add_argument("--h-order", type=int, default=8)
    s.add_argument("--dps", type=int, default=80)
    s = sub.add_parser("marked", help="central-window marked-law diagnostics")
    s.add_argument("--p", type=int, default=2)
    s.add_argument("--n", type=int, default=10**6)
    s.add_argument("--dps", type=int, default=80)
    s = sub.add_parser("inverse", help="fixed finite Newton iterations; no hidden root solve")
    s.add_argument("--p", type=int, default=2)
    s.add_argument("--n", type=int, default=10**6)
    s.add_argument("--order", type=int, default=4)
    s.add_argument("--steps", type=int, default=3)
    s.add_argument("--dps", type=int, default=80)
    s.add_argument("--exact-target", action="store_true")
    s = sub.add_parser("suite", help="small default reproduction suite; optional expensive deep checks")
    s.add_argument("--deep", action="store_true", help="also run p=1,2,3 at n=10000 and p=2,3 marked at 10^9")
    args = parser.parse_args()
    try:
        if args.command == "finite":
            out = finite_sum_diagnostic(args.p, args.n, args.order, args.h_order, args.dps)
        elif args.command == "marked":
            out = marked_diagnostic(args.p, args.n, args.dps)
        elif args.command == "inverse":
            out = newton_diagnostic(args.p, args.n, args.order, args.steps, args.dps, args.exact_target)
        else:
            out = {"preasymptotic_warning": WARNING_P3,
                   "finite": [finite_sum_diagnostic(p, 300, 4 if p == 1 else 8) for p in (1, 2, 3)],
                   "marked": [marked_diagnostic(p, 10**6) for p in (2, 3)],
                   "inverse": [newton_diagnostic(p, 10**6) for p in (1, 2, 3)]}
            if args.deep:
                out["deep_finite"] = [finite_sum_diagnostic(p, 10000, 4 if p == 1 else 12, 12, 90) for p in (1, 2, 3)]
                out["deep_marked"] = [marked_diagnostic(p, 10**9, 90) for p in (2, 3)]
        print(json.dumps(out, indent=2))
    except (ValueError, TypeError, RuntimeError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    _main()
