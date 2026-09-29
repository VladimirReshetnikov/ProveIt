#!/usr/bin/env python3
"""Exact coefficient checks for the quadratic-feedback inverse.
Only the standard library is needed for algebra; mpmath is used for diagnostics.
Coefficients are stored in exponential normalization n! [t^n] V(t).
The exact recurrence solves sum_j w_j V(t)^j exp(lambda_j*t)=t.
"""
from __future__ import annotations
import argparse, csv, json, math, time
from fractions import Fraction
from pathlib import Path
import mpmath as mp


def coefficients(N: int, a: int = 1, weights=None, slopes=None):
    if N < 1 or a < 1:
        raise ValueError('N and integer a must be positive')
    weights = weights or {}
    slopes = slopes or {}
    w = [0] + [weights.get(j, 1) for j in range(1, N + 1)]
    lam = [0] + [slopes.get(j, a*j*j) for j in range(1, N+1)]
    if w[1] != 1:
        raise ValueError('The first weight must be one')
    choose = [[math.comb(n, k) for k in range(n+1)] for n in range(N+1)]
    powers = [[pow(lam[j], k) for k in range(N+1)] for j in range(N+1)]
    # P[j][n] = n! [t^n] V(t)^j.
    P = [[0]*(N+1) for _ in range(N+1)]
    P[0][0] = 1
    v = [0]*(N+1)
    v[1] = P[1][1] = 1
    for n in range(2, N+1):
        bn = choose[n]
        for j in range(2, n+1):
            prev = P[j-1]
            P[j][n] = sum(bn[k]*v[k]*prev[n-k]
                           for k in range(1, n-j+2))
        total = 0
        for j in range(1, n+1):
            if not w[j]:
                continue
            upper = n-1 if j == 1 else n
            total += w[j]*sum(bn[k]*powers[j][n-k]*P[j][k]
                              for k in range(j, upper+1))
        v[n] = P[1][n] = -total
    return v


def compositions(n: int, prefix=()):
    if n == 0:
        yield prefix
    else:
        for d in range(1, n+1):
            yield from compositions(n-d, prefix+(d,))


def explicit_coefficient(n: int, a=1):
    """Independent finite ordered-composition formula, ordinary normalization."""
    ans = Fraction((-a)**(n-1), math.factorial(n-1))
    for D in range(1, n):
        k = n-D-1
        for ds in compositions(D):
            m = len(ds)
            beta = a*(sum(d*(d+1) for d in ds)-1)
            mult = Fraction(math.factorial(D+m),
                            math.factorial(D+1)*math.factorial(m))
            ans += (-1)**m*mult*Fraction(beta**k, math.factorial(k))
    return ans


def forward_coefficients(N: int, a: int):
    """Independent positive Lagrange formula, grouped by number of parts.
    Computes [q^n t^(m-1)] (sum_j q^j exp(a*j*j*t))^m / m.
    Exhaustive ordered compositions are used only at small degrees.
    """
    out = [Fraction(0)]*(N+1)
    for n in range(1, N+1):
        for js in compositions(n):
            m = len(js)
            out[n] += Fraction((a*sum(j*j for j in js))**(m-1),
                               math.factorial(m))
    return out


def mul(x, y, N):
    z = [Fraction(0)]*(N+1)
    for i, xi in enumerate(x[:N+1]):
        if xi:
            for j in range(min(len(y)-1,N-i)+1):
                z[i+j] += xi*y[j]
    return z


def composition_residual(v, a: int, N: int):
    u = forward_coefficients(N, a)
    vv = [Fraction(v[n],math.factorial(n)) for n in range(N+1)]
    ans = [Fraction(0)]*(N+1)
    power = [Fraction(0)]*(N+1); power[0]=1
    for j in range(1,N+1):
        power = mul(power,vv,N)
        for k in range(N+1): ans[k] += u[j]*power[k]
    return all(ans[k] == (1 if k==1 else 0) for k in range(N+1))


def two_core_one_tail(n: int, a: int):
    """n! times the positive-sign one-tail response L_(n,2).
    It is a signed finite sum; 'positive-sign' means V = Q - L + ... .
    """
    f = math.factorial(n)
    result = 0
    for j in range(3,n+1):
        for h in range(n-j+1):
            k=n-j-h
            beta=a*(j*j-j-1+2*h)
            result += (-1)**h*math.comb(2*h+j,h)*beta**k*(f//math.factorial(k))
    return result


def equivalent(n: int, a: int, c=None):
    aa=mp.mpf(a); nn=mp.mpf(n)
    c = aa+1 if c is None else mp.mpf(c)
    r=mp.findroot(lambda r: mp.log(r)+mp.log1p(r)+2*r-mp.log(aa*nn),
                  (max(mp.mpf('.01'),mp.log(nn)/5),max(mp.mpf('.1'),mp.log(nn))))
    D=2*r*r+4*r+1
    logS=nn*r*(1+2*r)/(1+r)-mp.log(D)/2
    return r, logS-c*r/aa


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--order',type=int,default=220)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args()
    if args.order < 20:
        parser.error('--order must be at least 20 to include all validation checks')
    args.output.mkdir(parents=True,exist_ok=True)
    mp.mp.dps=80
    started=time.time()
    scenarios=[('pure_a1',1,{},{}),('pure_a2',2,{},{}),
               ('signed_finite_core',1,{2:-2,3:3},{1:0,2:7}),
               ('cancelled_penalty',1,{2:-1},{})]
    rows=[]; exact={}; checks=[]
    for name,a,w,lam in scenarios:
        v=coefficients(args.order,a,w,lam)
        exact[name]=[str(x) for x in v]
        if not w and not lam:
            for n in range(1,13):
                assert explicit_coefficient(n,a)*math.factorial(n)==v[n]
                checks.append({'test':'ordered_composition','scenario':name,'n':n,'passed':True})
            assert composition_residual(v,a,11)
            checks.append({'test':'independent_U_of_V','scenario':name,'through':11,'passed':True})
        c=lam.get(1,a)+w.get(2,1)
        for n in sorted(set([20,40,80,120,160,args.order])):
            if n>args.order:continue
            r,logE=equivalent(n,a,c)
            ratio=-mp.mpf(v[n])/mp.factorial(n)*mp.exp(-logE)
            row={'scenario':name,'n':n,'a':a,'c':c,
                 'r':mp.nstr(r,20),'minus_v_over_equivalent':mp.nstr(ratio,20),
                 'sign_v':1 if v[n]>0 else -1 if v[n]<0 else 0}
            if name.startswith('pure'):
                L=two_core_one_tail(n,a)
                row['minus_v_over_two_core_response']=mp.nstr(-mp.mpf(v[n])/L,20)
            rows.append(row)
        print(name,'computed through',args.order,'elapsed',round(time.time()-started,2),flush=True)
    (args.output/'exact_coefficients.json').write_text(json.dumps(exact))
    with (args.output/'diagnostics.csv').open('w',newline='') as f:
        fields=sorted({key for row in rows for key in row})
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader();writer.writerows(rows)
    report={'exact_checks':checks,'number_of_exact_checks':len(checks),
            'order':args.order,'scenarios':[s[0] for s in scenarios],
            'elapsed_seconds':round(time.time()-started,3),
            'note':'Exact checks are finite algebraic tests, not proofs of asymptotic theorems. '
                   'Asymptotic diagnostics use floating-point mpmath, not interval arithmetic.'}
    (args.output/'verification.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(rows,indent=2))

if __name__=='__main__':main()
