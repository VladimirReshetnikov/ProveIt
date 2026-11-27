#!/usr/bin/env python3
"""Numerical illustration of the proved asymptotics, not a zeta-zero certificate.

The positive continuous spectral measure is
  dM(t) = (2*pi)^(-1) log(t/(2*pi)) 1_{t >= 2*pi} dt.
It has the same leading count as the zeta zeros, with kappa=1.
No assertion about simplicity of actual zeta zeros is used or tested here.
"""
from pathlib import Path
import csv
import json
import math
import warnings

import mpmath as mp
import numpy as np
from scipy.integrate import quad, IntegrationWarning
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
FIG = ROOT / "figures"
FIG.mkdir(exist_ok=True)
mp.mp.dps = 90
G = 2 * math.pi


def remainder_numerator(v):
    if abs(v) < 0.08:
        v2 = v*v
        return v2*v2*(1/24-v2/720+v2*v2/40320-v2**3/3628800+v2**4/479001600)
    return 0.5*v*v - 2*math.sin(v/2)**2


def integrate_remainder(h, logarithmic):
    """Integrate the scaled remainder without subtracting close covariances."""
    lo, b, split = G*h, h/2, 40.0
    def weight(v):
        return math.log(v/G) if logarithmic else 1.0
    def integrand(v):
        return weight(v)*remainder_numerator(v)/(v*v+b*b)**2
    cuts = sorted(set([lo] + [x for x in [0.08,0.5,1,2,4,8,16,24,32,split] if x>lo]))
    value = 0.0
    error = 0.0
    for a,z in zip(cuts[:-1], cuts[1:]):
        val,err=quad(integrand,a,z,epsabs=3e-12,epsrel=3e-12,limit=250)
        value += val
        error += err
    smooth,err1=quad(lambda v: weight(v)*(v*v/2-1)/(v*v+b*b)**2,
                     split,np.inf,epsabs=3e-12,epsrel=3e-12,limit=250)
    oscillatory,err2=quad(lambda v: weight(v)/(v*v+b*b)**2,
                         split,np.inf,weight="cos",wvar=1.0,
                         epsabs=3e-12,limlst=150,limit=250)
    return value+smooth+oscillatory, error+err1+err2


def remainder(h):
    h=float(h)
    j0,e0=integrate_remainder(h,False)
    j1,e1=integrate_remainder(h,True)
    value=mp.mpf(str(h))**3/mp.pi*(mp.log(1/mp.mpf(str(h)))*mp.mpf(str(j0))+mp.mpf(str(j1)))
    return value, h**3/math.pi*(abs(math.log(h))*e0+e1)


def main():
    warnings.simplefilter("error", IntegrationWarning)
    c0,_=quad(lambda t: math.log(t/G)/(math.pi*(t*t+0.25)**2),G,np.inf,
              epsabs=1e-14,epsrel=1e-12)
    d,_=quad(lambda t: math.log(t/G)*t*t/(math.pi*(t*t+0.25)**2),G,np.inf,
             epsabs=1e-14,epsrel=1e-12)
    c0,d=mp.mpf(str(c0)),mp.mpf(str(d))
    rows=[]
    for k in [2,3,4,5,6,8,10,12,16,20,24]:
        eps=mp.mpf(10)**(-k)
        r1,e1=remainder(eps)
        r2,e2=remainder(2*eps)
        x1=-d*eps**2/2+r1
        x2=-2*d*eps**2+r2
        large=(3*c0+x2+mp.sqrt((c0+x2)**2+8*(c0+x1)**2))/2
        determinant=c0*(r2-4*r1)-2*x1*x1
        small=determinant/large
        middle=2*d*eps**2-r2
        tau=eps**3*mp.log(1/eps)
        second_difference=2*(r2-4*r1)
        assert large>middle>small>0
        rows.append({"epsilon":str(eps),
                     "lambda1_over_3C0":float(large/(3*c0)),
                     "lambda2_over_2D_epsilon2":float(middle/(2*d*eps**2)),
                     "lambda3_over_tau":float(small/tau),
                     "second_difference_over_tau":float(second_difference/tau),
                     "quadrature_absolute_error_estimate_R1":e1,
                     "quadrature_absolute_error_estimate_R2":e2})
    target=1/9
    assert abs(rows[-1]["lambda3_over_tau"]-target)<0.01
    assert abs(rows[-1]["second_difference_over_tau"]-2/3)<0.06
    with (OUT/"continuum_results.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    result={"status":"passed numerical model checks",
            "scope":"Continuous positive spectral model, not actual zeta covariance; floating-point quadrature, not interval arithmetic.",
            "measure":"log(t/(2*pi))/(2*pi) dt for t >= 2*pi",
            "variance_C0":str(c0),"derivative_variance_D":str(d),
            "expected_lambda3_over_tau":"1/9",
            "expected_second_difference_over_tau":"2/3","rows":rows}
    (OUT/"continuum_results.json").write_text(json.dumps(result,indent=2)+"\n")
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                         "axes.spines.top":False,"axes.spines.right":False})
    fig,ax=plt.subplots(1,2,figsize=(10.5,3.7),constrained_layout=True)
    t=np.linspace(-1.25,1.25,501)
    hinge=np.maximum(t+1,0)-2*np.maximum(t,0)+np.maximum(t-1,0)
    ax[0].plot(t,hinge,color="#0e657c",lw=2.5)
    ax[0].fill_between(t,0,hinge**2,color="#0e657c",alpha=.18,
                       label=r"$\int S(t)^2\,dt=2/3$")
    ax[0].scatter([-1,0,1],[0,1,0],c="#0e657c",s=26,zorder=3)
    ax[0].set(xlabel="Offset t",ylabel="Hinge sum S(t)",
              title="Exact second-difference geometry",xlim=(-1.25,1.25),ylim=(0,1.13))
    ax[0].legend(frameon=False,loc="upper right")
    ks=[-math.log10(float(r["epsilon"])) for r in rows]
    vals=[9*r["lambda3_over_tau"] for r in rows]
    ax[1].plot(ks,vals,"o-",color="#aa5838",lw=1.8,ms=4,
               label=r"$9\lambda_3/(\varepsilon^3\log(1/\varepsilon))$")
    ax[1].axhline(1,color="#333333",ls="--",lw=1,label="Predicted limit = 1")
    ax[1].set(xlabel=r"$-\log_{10}\varepsilon$",ylabel="Normalized smallest eigenvalue",
              title="Continuous spectral model (not zero data)",ylim=(0.25,1.07))
    ax[1].legend(frameon=False,fontsize=8,loc="lower right")
    fig.savefig(FIG/"coalescence_geometry.pdf")
    fig.savefig(FIG/"coalescence_geometry.png",dpi=180)
    plt.close(fig)
    print(json.dumps({"status":result["status"],"rows":len(rows),
                      "last_lambda3_ratio":rows[-1]["lambda3_over_tau"],
                      "target":target},indent=2))


if __name__=="__main__":
    main()
