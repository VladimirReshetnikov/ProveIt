#!/usr/bin/env python3
"""Positive-recurrence diagnostics for the coefficient crossover.

Run alongside feedback_verify.py.  Use --output-dir to select a package's
data directory; relative output arguments are resolved against the current
working directory.  No installed or filed data are overwritten implicitly.

The stable density uses SciPy's S1 convention.  Its characteristic exponent
is (-i*t)**alpha, verified independently at three points by quadrature.
Floating-point diagnostics are not interval certificates.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
import platform
import time

import mpmath as mp
import numpy as np
import scipy
from scipy.stats import levy_stable, norm

from feedback_verify import f_coefficients, ld, number, poisson_coefficient


mp.mp.dps = 75


def scale_bn(s, n, b, a):
    if s < 3:
        return (n*mp.gamma(1-s)/b)**(1/(s-1))
    if s == 3:
        return mp.sqrt(mp.mpf(n)*mp.log(n)/(2*b))
    variance = mp.zeta(s-2)/b+a*a/(b**3)
    return mp.sqrt(n*variance)


def coordinate(s, n, b, a):
    return n*(1-a/b)/scale_bn(s,n,b,a)


def solve_b(s, n, xi, a):
    """Choose the root in a fixed neighborhood of the critical b=A.

    The finite-variance coordinate need not be monotone on all b>0.
    It is strictly increasing on [A/2,2A], the interval used here.
    """
    if xi == 0:
        return a
    lo, hi = a/2, 2*a
    assert coordinate(s,n,lo,a) < xi < coordinate(s,n,hi,a)
    for _ in range(240):
        b=(lo+hi)/2
        if coordinate(s,n,b,a) < xi:
            lo=b
        else:
            hi=b
    return (lo+hi)/2


def stable_density(xi, alpha=1.5):
    scale=(-math.cos(math.pi*alpha/2))**(1/alpha)
    return levy_stable.pdf(xi,alpha,1,loc=0,scale=scale)


def independent_density_check():
    alpha=mp.mpf("1.5")
    results=[]
    for xi in [-1,0,1]:
        if xi == 0:
            check=-1/mp.gamma(-1/alpha)
            route="closed Gamma value"
        else:
            integrand=lambda t: mp.re(mp.exp((-1j*t)**alpha-1j*xi*t))
            check=mp.quad(integrand,[0,1,2,4,8,16,32,64])/mp.pi
            route="75-digit direct Fourier quadrature"
        scipy_value=stable_density(xi)
        error=mp.mpf(str(scipy_value))/check-1
        assert abs(error)<mp.mpf("2e-12")
        results.append({"xi":xi,"scipy_density":float(scipy_value),
                        "independent_density":number(check,50),
                        "independent_route":route,
                        "relative_difference":number(error)})
    return results


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--indices",default="128,512,2048")
    parser.add_argument("--output-dir",type=Path,
        default=Path(__file__).resolve().parent/"feedback_crossover_numerics")
    args=parser.parse_args()
    indices=sorted(set(int(n) for n in args.indices.split(",")))
    if not indices or min(indices)<128:
        parser.error("this near-critical verification uses indices at least 128")
    started=time.perf_counter()
    # Explicitly fix SciPy's characteristic-function convention.
    levy_stable.parameterization="S1"
    density_checks=independent_density_check()
    rows=[]
    for sval in ["2.5","3","4"]:
        s=mp.mpf(sval)
        a=mp.zeta(s-1)
        for n in indices:
            for xi in [-1,0,1]:
                b=solve_b(s,n,mp.mpf(xi),a)
                u=mp.sqrt(b*b+2*mp.zeta(s))
                bn=scale_bn(s,n,b,a)
                xiactual=coordinate(s,n,b,a)
                coordinate_residual=xiactual-xi
                assert abs(coordinate_residual)<mp.mpf("1e-60")
                f=f_coefficients(s,u,n)
                scaled=poisson_coefficient(f,n,mp.mpf(1),u-b)
                density=(stable_density(xi) if s<3 else norm.pdf(xi))
                scaled_profile=np.longdouble(n)*ld(bn)*scaled
                ratio=scaled_profile/np.longdouble(str(density))
                row={
                    "s":sval,"n":n,"xi":xi,
                    "b":number(b,35),"u":number(u,35),
                    "A":number(a,35),"B_n":number(bn,35),
                    "boundary_radius":number(mp.exp(b-u),35),
                    "mean":number(a/b,35),
                    "coordinate_residual":number(coordinate_residual),
                    "scaled_coefficient_Rb_power_n":number(scaled),
                    "normalized_profile_n_Bn_Rb_power_n":number(scaled_profile),
                    "limiting_density":format(float(density),".17g"),
                    "ratio_to_limiting_density":number(ratio),
                }
                rows.append(row)
            print(f"s={sval}, n={n}: "+", ".join(
                f"xi={r['xi']}, ratio={r['ratio_to_limiting_density']}"
                for r in rows if r["s"]==sval and r["n"]==n),flush=True)
    profiles=[]
    xs=np.linspace(-3,3,241)
    stable=stable_density(xs)
    normal=norm.pdf(xs)
    for x,g,h in zip(xs,stable,normal):
        profiles.append({"xi":format(float(x),".12g"),
            "stable_alpha_1_5":format(float(g),".17g"),
            "standard_normal":format(float(h),".17g")})
    output={
        "status":"completed: finite positive recurrences and density diagnostics",
        "not_an_interval_certificate":True,
        "environment":{"python":platform.python_version(),
            "numpy":np.__version__,"scipy":scipy.__version__,
            "mpmath":mp.__version__,"mpmath_digits":mp.mp.dps,
            "longdouble_precision_digits":int(np.finfo(np.longdouble).precision)},
        "density_normalization":{
            "alpha":1.5,"scipy_parameterization":"S1","skewness_beta":1,
            "scale":"(-cos(pi*alpha/2))**(1/alpha)","location":0,
            "characteristic_exponent":"(-i*t)**alpha",
            "checks":density_checks},
        "rows":rows,"elapsed_seconds":time.perf_counter()-started,
    }
    args.output_dir.mkdir(parents=True,exist_ok=True)
    with (args.output_dir/"coefficient_crossover.json").open(
            "w",encoding="utf-8",newline="\n") as fh:
        json.dump(output,fh,indent=2,ensure_ascii=False);fh.write("\n")
    for filename,table in [("coefficient_crossover.csv",rows),
                           ("density_profiles.csv",profiles)]:
        with (args.output_dir/filename).open("w",encoding="utf-8",newline="") as fh:
            writer=csv.DictWriter(fh,fieldnames=list(table[0]),lineterminator="\n")
            writer.writeheader();writer.writerows(table)
    print(f"Completed in {output['elapsed_seconds']:.2f} seconds. Output: {args.output_dir}")


if __name__=="__main__":
    main()
