#!/usr/bin/env python3
"""Exact coefficient checks and non-certified asymptotic diagnostics.

The recurrence and partition comparisons use Python integers/Fraction only.
mpmath is used only to evaluate the asymptotic formula and display ratios.
These calculations are not a formal proof or directed interval arithmetic.
"""
from __future__ import annotations
import argparse, csv, json, math, platform, sys, time
from fractions import Fraction
from pathlib import Path
from typing import Iterator
import mpmath as mp

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def slopes(n: int, overrides: dict[int, int]) -> list[int]:
    if any(j < 1 or v < 0 for j, v in overrides.items()):
        raise ValueError('Overrides must have positive indices and nonnegative slopes.')
    return [0] + [overrides.get(j, j*j) for j in range(1,n+1)]


def scaled_coefficients(nmax: int, overrides: dict[int,int]) -> list[int]:
    """Return b[n] = n! [q^n] U using an integral exponential recurrence."""
    if nmax < 1:
        raise ValueError('The order must be positive.')
    lam=slopes(nmax,overrides)
    b=[0]*(nmax+1)
    exponentials=[[]]+[[1] for _ in range(nmax)]
    fact=[math.factorial(n) for n in range(nmax+1)]
    binom=[[]]+[[math.comb(m-1,k-1) for k in range(1,m+1)] for m in range(1,nmax+1)]
    for n in range(1,nmax+1):
        for j in range(1,n):
            m=n-j; row=exponentials[j]
            row.append(lam[j]*sum(binom[m][k-1]*b[k]*row[m-k] for k in range(1,m+1)))
        b[n]=sum((fact[n]//fact[n-j])*exponentials[j][n-j] for j in range(1,n+1))
    return b


def partitions(n: int, least: int=1) -> Iterator[tuple[int,...]]:
    if n == 0:
        yield ()
    else:
        for j in range(least,n+1):
            for rest in partitions(n-j,j):
                yield (j,)+rest


def partition_coefficient(n: int, overrides: dict[int,int]) -> Fraction:
    """Independent positive Lagrange formula, enumerating integer partitions."""
    lam=slopes(n,overrides); ans=Fraction(0)
    for part in partitions(n):
        multiplicities: dict[int,int]={}
        for j in part:
            multiplicities[j]=multiplicities.get(j,0)+1
        s=sum(lam[j] for j in part)
        den=math.prod(math.factorial(v) for v in multiplicities.values())
        ans += Fraction(s**(len(part)-1),den)
    return ans


def saddle(n: int) -> mp.mpf:
    """Solve 2r+log(r(r+1))=log n by safeguarded bisection."""
    if n < 1:
        raise ValueError('n must be positive.')
    target=mp.log(n); lo=mp.mpf('0'); hi=max(mp.mpf(1),target+1)
    for _ in range(4*mp.mp.dps+32):
        mid=(lo+hi)/2
        if 2*mid+mp.log(mid*(mid+1)) < target:
            lo=mid
        else:
            hi=mid
    return (lo+hi)/2


def log_equivalent(n: int, lambda1: int=1) -> tuple[mp.mpf,mp.mpf]:
    r=saddle(n); D=2*r*r+4*r+1
    return r, (2*r+1)*n*r/(r+1)+(lambda1+1)*r*r-mp.log(D)/2


def good_configuration_statistics(n: int, overrides: dict[int,int]) -> dict[str,int]:
    """Exact n!-scaled mass: exactly one part >=3, all others 1 or 2."""
    lam=slopes(n,overrides); fact=[math.factorial(k) for k in range(n+1)]
    total=0; giant_moment=0; two_moment=0
    for J in range(3,n+1):
        m=n-J
        for d in range(m//2+1):
            a=m-2*d; S=lam[J]+lam[1]*a+lam[2]*d
            w=(fact[n]//(fact[a]*fact[d]))*S**(a+d)
            total+=w; giant_moment+=J*w; two_moment+=d*w
    return {'mass':total,'giant_moment':giant_moment,'two_moment':two_moment}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    # Editorial amendment (ProveIt, 2026-09-29): all writers below emit LF line endings.
    parser.add_argument('--order',type=int,default=256)
    parser.add_argument('--check-order',type=int,default=18)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args()
    if not 1 <= args.check_order <= min(args.order,24):
        parser.error('check-order must lie between 1 and min(order,24).')
    mp.mp.dps=80; args.out.mkdir(parents=True,exist_ok=True)
    models={'quadratic':{},'lambda1_zero':{1:0},'lambda1_three':{1:3},'lambda2_seven':{2:7}}
    all_b={}; checks=[]; start=time.perf_counter()
    for name,overrides in models.items():
        b=scaled_coefficients(args.order,overrides); all_b[name]=b
        for n in range(1,args.check_order+1):
            direct=partition_coefficient(n,overrides)
            actual=Fraction(b[n],math.factorial(n))
            if direct != actual:
                raise AssertionError((name,n,direct,actual))
            checks.append({'model':name,'n':n,'passed':True})
        print(f'{name}: exact coefficients through {args.order}; checks passed',flush=True)
    with (args.out/'coefficients.csv').open('w',newline='') as f:
        writer=csv.writer(f,lineterminator='\n'); writer.writerow(['n']+list(models))
        for n in range(1,args.order+1):
            writer.writerow([n]+[str(Fraction(all_b[name][n],math.factorial(n))) for name in models])
    samples=sorted(set([n for n in [20,40,80,120,180,256,args.order] if n<=args.order]))
    diagnostics=[]
    for n in samples:
        for name,overrides in models.items():
            b=all_b[name][n]; r,loga=log_equivalent(n,overrides.get(1,1))
            logu=mp.log(b)-mp.loggamma(n+1)
            row={'model':name,'n':n,'r':mp.nstr(r,30),
                 'log_coefficient':mp.nstr(logu,35),
                 'exact_over_equivalent':mp.nstr(mp.exp(logu-loga),24)}
            if name=='quadratic' and n >= 3:
                good=good_configuration_statistics(n,overrides)
                assert 0 < good['mass'] <= b
                row.update({'one_giant_ones_twos_probability':mp.nstr(mp.mpf(good['mass'])/b,24),
                            'conditional_giant_mean':mp.nstr(mp.mpf(good['giant_moment'])/good['mass'],24),
                            'conditional_twos_mean':mp.nstr(mp.mpf(good['two_moment'])/good['mass'],24),
                            'predicted_giant_center':mp.nstr(n/(r+1),24),
                            'predicted_twos_mean':mp.nstr(r*r,24)})
            diagnostics.append(row)
    (args.out/'diagnostics.json').write_text(json.dumps(diagnostics,indent=2)+'\n',newline='\n')
    with (args.out/'asymptotic_ratios.csv').open('w',newline='') as f:
        writer=csv.writer(f,lineterminator='\n'); writer.writerow(['n','model','r','exact_over_equivalent'])
        for d in diagnostics:
            writer.writerow([d['n'],d['model'],d['r'],d['exact_over_equivalent']])
    ratios=[]
    for n in samples:
        r=saddle(n)
        base=all_b['quadratic'][n]
        ratios.append({'n':n,'lambda2_seven_over_base':mp.nstr(mp.mpf(all_b['lambda2_seven'][n])/base,24),
                       'lambda1_three_normalized':mp.nstr(mp.mpf(all_b['lambda1_three'][n])/base*mp.exp(-2*r*r),24),
                       'lambda1_zero_normalized':mp.nstr(mp.mpf(all_b['lambda1_zero'][n])/base*mp.exp(r*r),24)})
    (args.out/'finite_perturbations.json').write_text(json.dumps(ratios,indent=2)+'\n',newline='\n')
    report={'status':'all exact comparisons passed','order':args.order,
            'independent_exact_comparisons':len(checks),'checks':checks,
            'models':models,'arithmetic':'Python integers and fractions.Fraction',
            'diagnostics':'80-digit mpmath evaluations; not interval arithmetic',
            'python':platform.python_version(),'mpmath':mp.__version__,
            'elapsed_seconds':round(time.perf_counter()-start,3),
            'limits':['Finite computations do not prove the asymptotic theorems.',
                      'No Lean proof has been executed.',
                      'No Borel-Laplace remainder claim is numerically certified.']}
    (args.out/'verification.json').write_text(json.dumps(report,indent=2)+'\n',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('checks','models')},indent=2))

if __name__=='__main__':
    main()
