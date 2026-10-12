#!/usr/bin/env python3
"""Finite exact algebra and non-interval numerical diagnostics.

No numerical test substitutes for an all-order proof. Output is written only
to the requested directory, so historical evidence can be kept unchanged.
Python >=3.11; mpmath, sympy, numpy.
"""
from __future__ import annotations
import argparse, csv, json, math, platform, time
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import mpmath as mp
import numpy as np
import sympy as sp


def conv(a, b, n):
    c = [Q(0) for _ in range(n+1)]
    for i, x in enumerate(a[:n+1]):
        if x:
            for j, y in enumerate(b[:n+1-i]):
                if y: c[i+j] += x*y
    return c


def exp_series(a, n):
    assert a[0] == 0
    b = [Q(0) for _ in range(n+1)]; b[0] = Q(1)
    for k in range(1, n+1):
        b[k] = sum((j*a[j]*b[k-j] for j in range(1,k+1)),Q(0))/k
    return b


def li2_series(a, n):
    assert a[0] == 0
    p = [Q(0) for _ in range(n+1)]; p[0] = Q(1)
    ans = [Q(0) for _ in range(n+1)]
    for k in range(1,n+1):
        p = conv(p,a,n)
        ans = [x + y/(k*k) for x,y in zip(ans,p)]
    return ans


def laurent_coefficients(max_n):
    p = [Q(0)] + [Q(1,j*j) for j in range(1,max_n+1)]
    powers = [[Q(1)]+[Q(0)]*max_n]
    for k in range(1,max_n+1): powers.append(conv(powers[-1],p,max_n))
    out = {}
    for n in range(1,max_n+1):
        c = defaultdict(Q)
        for k in range(1,n+1):
            for j in range(k):
                c[k+j] += (powers[k][n]/k * math.comb(k+j-1,j)
                     * Q(n**(k-1-j), math.factorial(k-1-j)*2**j))
        out[n] = dict(c)
    return out


def fixed_point(u, n):
    v = [Q(0)]*(n+1)
    for _ in range(n+1):
        square = conv(v,v,n)
        e = exp_series(v,n)
        r_exp = [Q(0)] + e[:n]
        li = li2_series(r_exp,n)
        v = [x/(2*u)+y/u for x,y in zip(square,li)]
    return v


def exact_checks(max_n=10):
    count = 0; checks=[]
    coeff = laurent_coefficients(max_n)
    for n,c in coeff.items():
        assert set(c)==set(range(1,2*n)); count+=1
        assert all(x>0 for x in c.values()); count+=1
        assert c[1]==Q(1,n*n); count+=1
        assert c[2*n-1]==Q(math.comb(2*n-2,n-1),n*2**(n-1));count+=1
    for u in (1,2,3):
        v=fixed_point(Q(u),max_n)
        for n in range(1,max_n+1):
            a=sum((c*Q(1,u**p) for p,c in coeff[n].items()),Q(0))
            assert a==v[n]; count+=1
    checks.append('positive Laurent support, extreme coefficients, independent fixed-point replay')
    z=sp.symbols('z')
    for m in range(1,7):
        poly=sp.Integer(1)
        for k in range(1,m//2+1):
            poly += 2*(1-sp.Rational(2)**(1-2*k))*sp.zeta(2*k)*z**(2*k)
        top=2*(m//2+5)+1
        numerator=sp.series(sp.pi*z/sp.sin(sp.pi*z),z,0,top).removeO()-poly
        series=sp.expand((-1)**(m+1)*numerator/z**(m+1))
        for k in range(m//2+1,m//2+5):
            target=2*(-1)**(m+1)*(1-sp.Rational(2)**(1-2*k))*sp.zeta(2*k)
            assert sp.simplify(series.coeff(z,2*k-m-1)-target)==0;count+=1
        for n in range(1,5):
            residue=sp.simplify((-1)**(m+1)*n**(-sp.Integer(m)-1)*sp.pi*n/(sp.pi*(-1)**n))
            assert residue==sp.Rational((-1)**(m+n+1),n**m);count+=1
    checks.append('six Gamma/cosecant jet kernels: Taylor coefficients and positive residues')
    return coeff, {'assertions':count,'passed':True,'groups':checks}


@lru_cache(maxsize=None)
def eta_even(k):
    return (1-mp.power(2,1-2*k))*mp.zeta(2*k)


def borel_kernel(m, z):
    if abs(z)<mp.mpf('0.08'):
        return 2*(-1)**(m+1)*sum(eta_even(k)*z**(2*k-m-1)
               for k in range(m//2+1,m//2+49))
    poly=mp.mpf(1)+sum(2*eta_even(k)*z**(2*k) for k in range(1,m//2+1))
    return (-1)**(m+1)*(mp.pi*z/mp.sin(mp.pi*z)-poly)/z**(m+1)


def K(m,x):
    ans=x**m/mp.factorial(m)*(mp.log(x)-mp.digamma(m+1))
    for k in range(1,m//2+1):
        n=m-2*k
        ans+=2*eta_even(k)*x**n/mp.factorial(n)*(mp.log(x)-mp.digamma(n+1))
    return ans


def jet_diagnostics():
    rows=[]; ray=mp.exp(1j*mp.pi/6)
    for m,x in [(1,mp.mpf('1.5')),(2,mp.mpf('1.5')),(3,mp.mpf('4'))]:
        integral=mp.quad(lambda t:mp.exp(-x*ray*t)*borel_kernel(m,ray*t)*ray,
                         [0,mp.mpf('0.08'),mp.mpf('.4'),1,2,4,8,16,mp.inf])
        tail=-mp.polylog(m,-mp.exp(-x))
        tail_jet=mp.diff(lambda s:-mp.polylog(s,-mp.exp(-x)),m)
        # Differentiating the defining integral is an independent reference.
        # Tiny-step mp.diff(polylog, integer order) was observed to lose accuracy
        # for negative arguments outside the unit disk in mpmath 1.3.0.
        direct=mp.quad(lambda t:t**(m-1)*(mp.log(t)-mp.digamma(m))
                       /(1+mp.exp(t-x)),[0,1,x+2,12,mp.inf])/mp.gamma(m)
        reconstructed=K(m,x)+integral-(-1)**m*(tail_jet-1j*mp.pi*tail)
        err=abs(direct-reconstructed)
        assert err<mp.mpf('1e-42'), (m,x,err)
        rows.append({'m':m,'x':str(x),'absolute_error':mp.nstr(err,12),
                     'direct_order_derivative':mp.nstr(direct,35),
                     'upper_ray_imaginary_part':mp.nstr(mp.im(integral),20)})
    return rows


def characteristic(u):
    u=mp.mpf(u); lo=mp.mpf(0); hi=u
    for _ in range(240):
        mid=(lo+hi)/2
        val=mid*mid+2*mp.polylog(2,-mp.expm1(-mid))-u*u
        if val>0: hi=mid
        else: lo=mid
    w=(lo+hi)/2; t=-mp.expm1(-w)
    radius=mp.exp(-u)*mp.expm1(w)
    return w,t,radius


def radius_diagnostics():
    rows=[]
    for u in [mp.mpf('.7'),mp.mpf(1),mp.pi/mp.sqrt(6),mp.mpf(2),mp.mpf(4),mp.mpf(8)]:
        w,t,r=characteristic(u)
        residual=abs(w*w+2*mp.polylog(2,t)-u*u)
        assert residual<mp.mpf('1e-55')
        rows.append({'u':mp.nstr(u,24),'w':mp.nstr(w,24),'radius':mp.nstr(r,24),
                     'physical_over_radius':mp.nstr(mp.exp(-u)/r,24),
                     'characteristic_residual':mp.nstr(residual,8)})
    w,t,r=characteristic(mp.pi/mp.sqrt(6))
    assert abs(t-mp.mpf('.5'))<mp.mpf('1e-55')
    return rows


def scaled_large_n(max_n):
    """Positive convolutions; binary64 diagnostic, not certified asymptotics."""
    rows=[]; targets=[n for n in (16,32,64,128,256,512) if n<=max_n]
    for u in (2.,4.):
        w,t,r=characteristic(mp.mpf(u)); R=float(r)
        p=np.zeros(max_n+1)
        for j in range(1,max_n+1):p[j]=R**j/(j*j)
        A=np.zeros((max_n+1,max_n+1)); A[0,0]=1.
        for k in range(1,max_n+1):A[k,:]=np.convolve(A[k-1,:],p)[:max_n+1]
        constant=float(mp.sqrt(w*(1-t)/(2*mp.pi)))
        for n in targets:
            total=0.
            for k in range(1,n+1):
                z=math.exp((k-1)*math.log(n)-math.lgamma(k)-k*math.log(u)); s=z
                for j in range(k-1):
                    z *= (k+j)*(k-1-j)/(2*u*n*(j+1)); s+=z
                total+=A[k,n]*s/k
            ratio=total*n**1.5/constant
            assert math.isfinite(ratio) and ratio>0
            rows.append({'u':u,'N':n,'normalized_coefficient':ratio})
    return rows


def inverse_diagnostics():
    coeff=laurent_coefficients(24); rows=[]
    for u in (mp.mpf(2),mp.mpf(4)):
        y=u*u/2+mp.pi**2/6
        direct=mp.findroot(lambda x:-mp.polylog(2,-mp.exp(x))-y,(u,u+mp.mpf('.2')))
        s=u
        for n in range(1,25):
            a=sum(mp.mpf(c.numerator)/c.denominator/u**p for p,c in coeff[n].items())
            s+=(-1)**(n-1)*a*mp.exp(-n*u)
            if n in (4,8,12,24):
                rows.append({'u':str(u),'N':n,'absolute_inverse_error':mp.nstr(abs(s-direct),12),
                             'residual':mp.nstr(abs(-mp.polylog(2,-mp.exp(s))-y),12)})
        assert abs(s-direct)<mp.mpf('1e-13')
    return rows


def jet_bell_diagnostics():
    rows=[]
    for m,n in [(1,1),(1,3),(2,2),(3,3)]:
        k=(n+m)//2; x=mp.mpf('2.3')
        b1=mp.log(x)+mp.euler-mp.harmonic(n-1)
        h2=sum(mp.mpf(1)/j**2 for j in range(1,n)); b2=-mp.zeta(2)-h2
        base=2*(-1)**(m+1)*eta_even(k)*mp.gamma(n)*x**(-n)
        f=lambda e:2*eta_even(k)*mp.rgamma(1-n+e)*x**(-n+e)
        for order,factor in [(1,1),(2,2*b1),(3,3*(b1*b1+b2))]:
            error=abs(mp.diff(f,0,order)-base*factor)
            assert error<mp.mpf('1e-52')
            rows.append({'m':m,'n':n,'order':order,'error':mp.nstr(error,8)})
    return rows



def periodic_diagnostics():
    rows=[]
    for c in [(1,0,0),(1,-2,0,3)]:
        d=len(c); z=mp.mpc('.17','.13'); x=mp.mpf('1.3')
        L=lambda j:sum(c[a-1]*mp.zeta(j,mp.mpf(a)/d) for a in range(1,d+1))/d**j
        for m in (1,2,3):
            diff=sum(c[a-1]*(mp.digamma((a-z)/d)-mp.digamma((a+z)/d))
                         for a in range(1,d+1))/d
            closed=(-1)**m/z**m*(diff+sum(2*L(2*k)*z**(2*k-1) for k in range(1,m//2+1)))
            series=2*(-1)**(m+1)*sum(L(2*k)*z**(2*k-m-1)
                                     for k in range(m//2+1,m//2+61))
            kernel_error=abs(closed-series)
            omega=mp.exp(2j*mp.pi/d)
            fourier=sum(sum(c[a-1]*omega**(-p*a) for a in range(1,d+1))/d
                        *mp.polylog(m,omega**p*mp.exp(-x)) for p in range(d))
            direct=sum(c[(n-1)%d]*mp.exp(-n*x)/n**m for n in range(1,180))
            tail_error=abs(fourier-direct)
            assert kernel_error<mp.mpf('1e-53') and tail_error<mp.mpf('1e-53')
            rows.append({'period':d,'weights':str(c),'m':m,
                         'kernel_error':mp.nstr(kernel_error,10),'DFT_tail_error':mp.nstr(tail_error,10)})
    return rows


def write_csv(path, rows):
    if not rows:return
    with path.open('w',encoding='utf-8',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n')
        writer.writeheader();writer.writerows(rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path('data'))
    parser.add_argument('--max-n',type=int,default=256)
    parser.add_argument('--skip-borel',action='store_true',help='Omit slow quadrature; explicitly recorded as skipped.')
    args=parser.parse_args()
    if not 16<=args.max_n<=512:parser.error('--max-n must lie between 16 and 512')
    out=args.output_dir;out.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=65; eta_even.cache_clear(); start=time.time()
    coeff,exact=exact_checks();print('exact:',exact,flush=True)
    (out/'coefficients.json').write_text(json.dumps({str(n):{str(p):str(c) for p,c in d.items()}
                for n,d in coeff.items()},indent=2)+'\n')
    radii=radius_diagnostics();write_csv(out/'radii.csv',radii);print('radii passed',flush=True)
    inverse=inverse_diagnostics();write_csv(out/'inverse.csv',inverse);print('inverse passed',flush=True)
    large=scaled_large_n(args.max_n);write_csv(out/'large_sector.csv',large);print('large-N computed',flush=True)
    bell=jet_bell_diagnostics();print('Bell jets passed',flush=True)
    periodic=periodic_diagnostics();write_csv(out/'periodic.csv',periodic);print('periodic kernels passed',flush=True)
    jets=[] if args.skip_borel else jet_diagnostics()
    write_csv(out/'borel_jets.csv',jets);print('Borel jets:', 'SKIPPED' if args.skip_borel else 'passed',flush=True)
    report={'status':'passed_with_borel_skipped' if args.skip_borel else 'passed',
      'scope':'Finite exact identities and non-interval numerical diagnostics; not formal proofs',
      'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,'numpy':np.__version__,
      'mpmath_dps':mp.mp.dps,'exact':exact,'borel_jets':jets,'bell_jets':bell,'periodic_kernels':periodic,
      'radius_checks':len(radii),'inverse_checks':len(inverse),'large_sector_rows':len(large),
      'max_n':args.max_n,'elapsed_seconds':round(time.time()-start,2)}
    (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'run_summary.txt').write_text(f"PASS: {exact['assertions']} exact assertions; "
         f"{len(jets)} complex-ray Borel reconstructions; {len(bell)} order-jet comparisons; "
         f"{len(radii)} radius and {len(inverse)} inverse diagnostics.\n"
         f"Periodic kernels and Fourier tails: {len(periodic)} paired diagnostics.\n"
         f"Large-sector asymptotic ratios: {len(large)} rows through N={args.max_n}.\n"
         f"Borel quadrature skipped: {args.skip_borel}.\n"
         "All floating-point results are diagnostics, not interval certificates.\n")
    print((out/'run_summary.txt').read_text())

if __name__=='__main__':main()
