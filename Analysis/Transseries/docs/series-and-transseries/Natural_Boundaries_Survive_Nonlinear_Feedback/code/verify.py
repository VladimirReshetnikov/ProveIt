#!/usr/bin/env python3
"""Reproducible finite checks for the feedback natural-boundary article.

Exact rational checks establish finite identities only.  Optional high-precision
checks are diagnostics, not interval certificates or proofs of asymptotic limits.
No network access is used.  Python >=3.10; mpmath is optional.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECORDED = ROOT / "data"
# ed. 2026-09-29: outputs go to rerun/ unless --output-dir is given; writing
# into the recorded data/ needs --overwrite-recorded. All files are LF.
DATA = ROOT / "rerun"

def mul(a: list[F], b: list[F], n: int) -> list[F]:
    c = [F(0)] * (n + 1)
    for i, x in enumerate(a[:n+1]):
        if x:
            for j, y in enumerate(b[:n+1-i]):
                if y:
                    c[i+j] += x*y
    return c

def compose(a: list[F], b: list[F], n: int) -> list[F]:
    out = [F(0)] * (n+1)
    for x in reversed(a[:n+1]):
        out = mul(out,b,n)
        out[0] += x
    return out

def exp_series(a: list[F], n: int) -> list[F]:
    if a[0] != 0:
        raise ValueError("The constant term must vanish.")
    b = [F(1)] + [F(0)] * n
    for k in range(1,n+1):
        b[k] = sum((i*a[i]*b[k-i] for i in range(1,k+1)),F(0))/k
    return b

def feedback(d: int, n: int) -> list[F]:
    """Compute each next coefficient independently from the defining equation."""
    u = [F(0)] * (n+1)
    for k in range(1,n+1):
        for j in range(1,k+1):
            scaled = [F(j**d)*x for x in u[:k-j+1]]
            u[k] += exp_series(scaled,k-j)[k-j]
    return u

def inverse(a: list[F], n: int) -> list[F]:
    if a[0] or a[1] != 1:
        raise ValueError("Only tangent-to-identity series are supported.")
    b = [F(0),F(1)] + [F(0)]*(n-1)
    for k in range(2,n+1):
        b[k] = -compose(a,b,k)[k]
    return b

def poly_mul_int(a: dict[int,int], b: dict[int,int]) -> dict[int,int]:
    c: dict[int,int] = {}
    for i,x in a.items():
        for j,y in b.items():
            c[i+j] = c.get(i+j,0)+x*y
    return {k:v for k,v in c.items() if v}

def block_series(d: int, n: int) -> list[dict[int,int]]:
    """Coefficient polynomials H_k(v), from P=t-sum(P^j v^(j^d-j))."""
    h: list[dict[int,int]] = [{} for _ in range(n+1)]
    h[1]={0:1}
    for k in range(2,n+1):
        power: list[dict[int,int]] = [{} for _ in range(k+1)]
        power[0]={0:1}
        acc: dict[int,int] = {}
        for j in range(1,k+1):
            nxt: list[dict[int,int]] = [{} for _ in range(k+1)]
            for a in range(k+1):
                if power[a]:
                    for b in range(1,k-a+1):
                        if h[b]:
                            prod=poly_mul_int(power[a],h[b])
                            for e,v in prod.items():
                                nxt[a+b][e]=nxt[a+b].get(e,0)+v
            power=nxt
            if j>=2:
                for e,v in power[k].items():
                    ee=e+j**d-j
                    acc[ee]=acc.get(ee,0)-v
        h[k]={e:v for e,v in acc.items() if v}
    return h

def tree_counts(n: int) -> list[int]:
    # C=t+C^2/(1-C), equivalently 2C^2-(1+t)C+t=0.
    c=[0]*(n+1)
    c[1]=1
    for k in range(2,n+1):
        c[k]=2*sum(c[j]*c[k-j] for j in range(1,k))-c[k-1]
    return c

def exact_checks(order: int) -> dict:
    count=0
    rows=[]
    blocks_out={}
    for d in (2,3,4):
        u=feedback(d,order)
        q=inverse(u,order)
        ident=[F(0),F(1)]+[F(0)]*(order-1)
        for composed in (compose(u,q,order),compose(q,u,order)):
            for a,b in zip(composed,ident):
                assert a==b
                count+=1
        # The defining equation in the inverse coordinates, independently.
        rhs=[F(0)]*(order+1)
        power=[F(1)]+[F(0)]*order
        for j in range(1,order+1):
            power=mul(power,q,order)
            e=[F((j**d)**k,math.factorial(k)) for k in range(order+1)]
            term=mul(power,e,order)
            rhs=[a+b for a,b in zip(rhs,term)]
        for a,b in zip(rhs,ident):
            assert a==b
            count+=1
        assert q[2]==-2 and q[3]==F(9,2)-2**d
        count+=2
        for k in range(1,order+1):
            rows.append([d,k,str(u[k]),str(q[k])])
        nb=min(order,10)
        h=block_series(d,nb)
        counts=tree_counts(nb)
        p=[F(0)]*(nb+1)
        for k in range(1,nb+1):
            assert all(0<=e<=k**d-k for e in h[k])
            assert sum(abs(v) for v in h[k].values())<=counts[k]
            count+=2
            for m in range(nb-k+1):
                p[k+m]+=sum((F(v*e**m,math.factorial(m)) for e,v in h[k].items()),F(0))
        q_block=mul(p,[F((-1)**k,math.factorial(k)) for k in range(nb+1)],nb)
        for a,b in zip(q_block,q):
            assert a==b
            count+=1
        blocks_out[str(d)]={str(k):h[k] for k in range(1,nb+1)}
    with (DATA/"coefficients.csv").open("w",newline="") as f:
        w=csv.writer(f,lineterminator="\n");w.writerow(["d","n","U_coefficient_exact","Q_coefficient_exact"]);w.writerows(rows)
    (DATA/"blocks.json").write_text(json.dumps(blocks_out,indent=2)+"\n",newline="\n")
    return {"status":"passed","rational_comparisons":count,"order":order,"degrees":[2,3,4],
            "scope":"Finite exact identities, not an infinite-series or theorem verification."}

def eulerian_polynomials(n: int) -> list[list[int]]:
    # Li_{-m}(z)=z A_m(z)/(1-z)^(m+1), m>=1.
    out=[[1],[1]]
    for m in range(2,n+1):
        old=out[-1];new=[0]*m
        for k in range(m):
            new[k]=(k+1)*(old[k] if k<len(old) else 0)+(m-k)*(old[k-1] if k else 0)
        out.append(new)
    return out

def numerical_checks() -> dict:
    try:
        import mpmath as mp
    except ImportError:
        return {"status":"not run","reason":"Optional mpmath is not installed."}
    mp.mp.dps=110
    def s(z):
        return mp.nstr(z,45)
    def li_neg(m,z,polys):
        if m==0:return z/(1-z)
        p=mp.mpc(0)
        for v in reversed(polys[m]):p=p*z+v
        return z*p/(1-z)**(m+1)
    polys=eulerian_polynomials(240)
    # Moving-curve asymptotics: q(v)=q0 exp(h1 v+h2 v^2).
    curve_rows=[]
    cases=[(2,mp.mpf(1)/5,mp.mpf(3)/7,mp.mpf(1)/9),
           (3,mp.mpf(1)/30,mp.mpf(3)/7,mp.mpf(1)/9)]
    for d,q0,h1,h2 in cases:
        moments=[li_neg(m,q0,polys) for m in range(241)]
        a=-mp.log(q0)
        for n in (8,16,32,64,80):
            value=mp.mpc(0)
            for r in range(n//2+1):
                ell=n-2*r
                for k in range(ell+1):
                    m=d*ell-(d-1)*k+r
                    value+=(h2**r/mp.factorial(r))*(mp.binomial(ell,k)*h1**k/mp.factorial(ell))*moments[m]
            amp=mp.exp(a*h1/2) if d==2 else 1
            lead=mp.factorial(d*n)/mp.factorial(n)*a**(-d*n-1)*amp
            ratio=value/lead
            curve_rows.append([d,n,s(mp.re(ratio)),s(mp.im(ratio))])
        assert abs(ratio-1)<mp.mpf('0.12')
    with (DATA/"moving_curve_ratios.csv").open("w",newline="") as f:
        w=csv.writer(f,lineterminator="\n");w.writerow(["d","n","ratio_real","ratio_imag"]);w.writerows(curve_rows)
    # Exact periodic boundary equation, evaluated with high precision.
    boundary=[]
    maxres=mp.mpf(0)
    for b in (127,257,509,1021):
        t=2*mp.pi/b;u=1j*t
        phases=[mp.exp(u*(j*j%b)) for j in range(1,b+1)]
        # exp(u*(j*j % b)) equals exp(2 pi i j^2/b).
        def rat(q):
            p=mp.mpc(0)
            for v in reversed(phases):p=(p+v)*q
            return p/(1-q**b)
        q=mp.findroot(lambda z:rat(z)-u,(u,u+2*t*t),solver='secant',tol=mp.mpf('1e-100'))
        res=abs(rat(q)-u);maxres=max(maxres,res)
        assert res<mp.mpf('1e-95')
        approx=u-2*u*u+u**3/2-F(2,3).numerator/mp.mpf(F(2,3).denominator)*u**4
        boundary.append([b,s(t),s(mp.re(q)),s(mp.im(q)),s(mp.re(q)/(t*t)),s(abs(q-approx)/t**5),s(res)])
    with (DATA/"boundary_points.csv").open("w",newline="") as f:
        w=csv.writer(f,lineterminator="\n");w.writerow(["denominator","t","Re_Q_it","Im_Q_it","Re_Q_over_t2","four_term_error_over_t5","residual"]);w.writerows(boundary)
    # Finite Fourier spectra and the odd-modulus quadratic Gauss magnitude.
    gaussmax=mp.mpf(0);gauss_cases=0
    for b in (3,5,7,9,11,15):
        for a in range(1,b):
            if math.gcd(a,b)!=1:continue
            for r in range(b):
                g=sum(mp.exp(2j*mp.pi*(a*j*j-r*j)/b) for j in range(b))/b
                err=abs(abs(g)**2-mp.mpf(1)/b)
                gaussmax=max(gaussmax,err);gauss_cases+=1
    assert gaussmax<mp.mpf('1e-95')
    # Tied nearest poles: alternating coefficients do not permit cancellation.
    q0=-mp.mpf(1)/5
    a1=-mp.log(abs(q0))+1j*mp.pi;a2=mp.conj(a1);rho=abs(a1)
    tie=[]
    for n in range(1,401):
        val=(rho/a1)**(2*n)/a1+(rho/a2)**(2*n)/a2
        tie.append(abs(val)**2)
    expected=2/abs(a1)**2
    mean=sum(tie)/len(tie)
    assert abs(mean-expected)<mp.mpf('0.003')
    return {"status":"passed","precision_decimal_digits":mp.mp.dps,
            "moving_curve_cases":len(curve_rows),"boundary_points":len(boundary),
            "max_boundary_residual":s(maxres),"gauss_checks":gauss_cases,
            "max_gauss_error":s(gaussmax),"tied_pole_mean_square":s(mean),
            "tied_pole_predicted_mean_square":s(expected),
            "scope":"High-precision, non-interval diagnostics; not certified decimal enclosures."}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order",type=int,default=24)
    parser.add_argument("--exact-only",action="store_true")
    parser.add_argument("--output-dir",type=Path,default=ROOT/"rerun")
    parser.add_argument("--overwrite-recorded",action="store_true",
                        help="allow writing into the recorded data/ directory")
    args=parser.parse_args()
    if not 4<=args.order<=60:parser.error("--order must be between 4 and 60")
    try:  # ed. 2026-09-29: LF also in redirected stdout on Windows
        sys.stdout.reconfigure(newline="\n")
    except AttributeError:
        pass
    global DATA
    DATA=args.output_dir
    if DATA.resolve()==RECORDED.resolve() and not args.overwrite_recorded:
        parser.error("refusing to overwrite the recorded data/; pass --overwrite-recorded or choose another --output-dir")
    DATA.mkdir(parents=True,exist_ok=True)
    result={"python":platform.python_version(),"exact":exact_checks(args.order),
            "numerical":({"status":"not run","reason":"--exact-only"} if args.exact_only else numerical_checks())}
    (DATA/"verification.json").write_text(json.dumps(result,indent=2)+"\n",newline="\n")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
