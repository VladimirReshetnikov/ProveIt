"""Independent numeric checks for the moving-Gamma-zero jet formulas.

The root-jet prediction uses an Eulerian/Stirling reduction and binomial
Hurwitz-zeta tails. The comparison extracts derivatives of the original
spectral product by a Cauchy contour. These are diagnostics, not a proof.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp

mp.mp.dps = 65
BASE = Path(__file__).resolve().parent.parent / "results"


def stirling2(n: int, k: int) -> int:
    row = [1] + [0] * k
    for j in range(1, n + 1):
        row = [0] + [row[h - 1] + h * row[h] for h in range(1, k + 1)]
    return row[k]


def log_coordinate_series(r: int, k: int, x, cut: int = 12, terms: int = 58):
    """L_r when k=1, M_{r,k} for k>=2, via binomial tail."""
    x = mp.mpf(x)
    cut = max(cut, int(mp.ceil(4*abs(x))))
    if k == 1:
        if r == 0:
            return mp.mpf(0)
        total = mp.fsum((mp.log(n+x)**r-mp.log(n)**r)/n
                        for n in range(1,cut+1))
    else:
        total = mp.fsum(mp.log(n+x)**r/mp.mpf(n)**k
                        for n in range(1,cut+1))
        total += (-1)**r * mp.diff(lambda v: mp.zeta(v,cut+1),k,r)
    # e[j] = elementary symmetric polynomial of degree j in 1,...,1/(h-1).
    e = [mp.mpf(1)] + [mp.mpf(0)]*max(0,r-1)
    for h in range(1,terms+1):
        coefficient = mp.fsum(
            (math.factorial(r)//math.factorial(r-j)) * e[j-1]
            *mp.diff(lambda v: mp.zeta(v,cut+1),k+h,r-j)
            for j in range(1,min(r,h)+1))
        total += (-1)**r * (-x)**h / h * coefficient
        for j in range(min(r-1,h),0,-1):
            e[j] += e[j-1]/h
    return total


def b_from_coordinates(r: int, a, m: int):
    a=mp.mpf(a); x=a+m
    value=x*(mp.stieltjes(r)+log_coordinate_series(r,1,x))
    for k in range(2,r+1):
        value += (math.factorial(k-1)*stirling2(r,k)*x**k
                  *log_coordinate_series(r,k,x))
    for j in range(1,m+1):
        value += mp.log(x-j)**r * mp.fsum(
            math.factorial(k-1)*stirling2(r,k)*(-x/j)**k
            for k in range(1,r+1))
    return (-1)**(r+1)*value


def bell(xs):
    values=[mp.mpf(1)]
    for n in range(1,len(xs)+1):
        values.append(mp.fsum(math.comb(n-1,k-1)*xs[k-1]*values[n-k]
                              for k in range(1,n+1)))
    return values[-1]


def predict_jets(a,m,order=4):
    a=mp.mpf(a); x=a+m; ell=mp.log(x)
    h0=x*mp.gamma(a)*(-1)**m*math.factorial(m)
    bs=[b_from_coordinates(r,a,m) for r in range(1,order)]
    cs=[b + mp.bernpoly(r,0)*ell**r/r for r,b in enumerate(bs,1)]
    jets=[h0*ell*r*bell(cs[:r-1]) for r in range(1,order+1)]
    return jets,bs


def spectral_product(s,a,x,cut=18,terms=68):
    # Finite factors and the normally convergent Hurwitz tail are the
    # original spectral product, with its specified Laurent subtraction.
    cut = max(cut,int(mp.ceil(6*x-a)))
    q=a+cut
    regular=mp.zeta(s,q)-1/(s-1)
    exponent=-x*regular-mp.fsum(x**k*mp.zeta(k*s,q)/k
                              for k in range(2,terms+1))
    return mp.fprod(1-x*(a+n)**(-s) for n in range(cut))*mp.exp(exponent)


def cauchy_jets(a,m,order=4,nodes=64,radius=mp.mpf('0.023')):
    a=mp.mpf(a); x=a+m
    # Sample halfway between the roots of unity so no point lies at s=1.
    values=[]
    for j in range(nodes):
        theta=2*mp.pi*(mp.mpf(j)+mp.mpf('0.5'))/nodes
        w=mp.exp(1j*theta)
        values.append((w,spectral_product(1+radius*w,a,x)))
    return [math.factorial(r)*mp.fsum(value/w**r for w,value in values)
            /nodes/radius**r for r in range(1,order+1)]


def fmt(z):
    return mp.nstr(z,55)


def run():
    records=[]
    for a,m in [('0.5',0),('1',1),('0.7',2),('1',0)]:
        predicted,bs=predict_jets(a,m)
        observed=cauchy_jets(a,m)
        x=mp.mpf(a)+m
        d_integral=mp.quad(lambda t: mp.zeta(2) if t==0
                          else (mp.digamma(1+t)+mp.euler)/t,[0,x])
        b1_integral=x*(mp.stieltjes(1)+d_integral-mp.fsum(
            mp.log(x-j)/j for j in range(1,m+1)))
        records.append({'a':a,'m':m,
                        'b1_digamma_integral_error':fmt(abs(bs[0]-b1_integral)),
                        'jets':[{'order':r,'predicted':fmt(p),
                                 'cauchy':fmt(q),'abs_error':fmt(abs(p-q))}
                                for r,(p,q) in enumerate(zip(predicted,observed),1)]})
        print(f'a={a}, m={m}, max jet error '
              f'{mp.nstr(max(abs(p-q) for p,q in zip(predicted,observed)),5)}',
              flush=True)
    # Differential closure: compare termwise differentiated binomial tails
    # against the finite triangular recurrence at an interior positive x.
    x=mp.mpf('0.6'); closure=[]
    def L(r): return log_coordinate_series(r,1,x)
    for r in [1,2,3]:
        observed=mp.diff(lambda y:log_coordinate_series(r,1,y),x)
        predicted=r*(L(r-1)+mp.stieltjes(r-1)-mp.stieltjes(r-1,1+x))/x
        closure.append({'family':'L','r':r,'error':fmt(abs(observed-predicted))})
    for r,k in [(1,2),(2,2),(2,3),(3,3)]:
        observed=mp.diff(lambda y:log_coordinate_series(r,k,y),x)
        block=L(r-1)+mp.stieltjes(r-1)-mp.stieltjes(r-1,1+x)
        predicted=r*(mp.fsum((-1)**(k-j)*log_coordinate_series(r-1,j,x)
                             /x**(k-j+1) for j in range(2,k+1))
                     +(-1)**(k-1)*block/x**k)
        closure.append({'family':'M','r':r,'k':k,'error':fmt(abs(observed-predicted))})
    assert all(mp.mpf(j['abs_error']) < mp.mpf('1e-35') for row in records for j in row['jets'])
    assert all(mp.mpf(row['b1_digamma_integral_error']) < mp.mpf('1e-35') for row in records)
    assert all(mp.mpf(row['error']) < mp.mpf('1e-50') for row in closure)
    result={'dps':mp.mp.dps,'root_checks':records,'primitive_closure_checks':closure,
            'status':'numerical diagnostics; proofs are in sections/05-gamma-roots.tex'}
    (BASE/'moving_zero_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Saved moving_zero_checks.json',flush=True)


if __name__=='__main__':
    run()
