#!/usr/bin/env python3
"""Independent exact and numerical checks for the A273821 article.

Run: python code/verify.py [--brute-max 9] [--dp-max 120]
Requires Python 3.10+, mpmath, sympy. Numerical checks support but do not
replace the proofs in article.tex. No network access is used.
"""
from __future__ import annotations
import argparse
import csv
import itertools
import json
import math
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def catalan(n: int) -> int:
    if n < 0:
        return 0
    return math.comb(2*n,n)//(n+1)

def choose(n: int, k: int) -> int:
    return math.comb(n,k) if 0 <= k <= n else 0

def entry(n: int, k: int) -> int:
    """Exact formula; offset n>=1, 1<=k<=n."""
    if not 1 <= k <= n:
        return 0
    if n == k:
        return 1 << (n-1)
    ell = n-k
    return (1 << (k-1))*math.comb(2*ell,ell-1)-math.comb(n+ell-1,ell-1)

def tail(n: int, k: int) -> int:
    if not 1 <= k <= n:
        return catalan(n) if k <= 1 else 0
    ell = n-k
    return (1 << (k-1))*math.comb(2*ell+1,ell)-choose(n+ell,ell-1)

def avoids_123(p: tuple[int, ...]) -> bool:
    # Independent two-threshold test for an increasing subsequence of length 3.
    small = middle = len(p)+1
    for a in p:
        if a < small:
            small = a
        elif a < middle:
            middle = a
        else:
            return False
    return True

def statistic(p: tuple[int, ...]) -> int:
    # A 132 occurrence enters the restriction when its smallest value enters.
    n = len(p)
    highest_minimum = 0
    for i in range(n):
        for j in range(i+1,n):
            for h in range(j+1,n):
                if p[i] < p[h] < p[j]:
                    highest_minimum = max(highest_minimum,p[i])
    return n-highest_minimum

def brute_checks(max_n: int) -> int:
    total = 0
    for n in range(1,max_n+1):
        row = [0]*(n+1)
        for p in itertools.permutations(range(1,n+1)):
            total += 1
            if avoids_123(p):
                row[statistic(p)] += 1
        assert row[1:] == [entry(n,k) for k in range(1,n+1)], (n,row)
        assert sum(row) == catalan(n)
    return total

def insertion_checks(max_n: int) -> int:
    # Each state is (d,k), with k=0 meaning no 132 has occurred yet.
    # Independent transition implementation, not the binomial formula.
    states = {(1,0):1}
    entries = 0
    for n in range(1,max_n+1):
        row = [0]*(n+1)
        for (d,k),v in states.items():
            row[n if k == 0 else k] += v
        assert row[1:] == [entry(n,k) for k in range(1,n+1)], n
        assert sum(row) == catalan(n)
        assert all(sum(row[k:]) == tail(n,k) for k in range(1,n+1))
        z2 = sum(row[k]*(1<<k) for k in range(1,n+1))
        assert z2 == (n+2)*math.comb(2*n,n)-(1<<(2*n))
        # Independent weighted moments and the critical mean identity.
        first = sum(k*row[k]*(1<<k) for k in range(1,n+1))
        assert 6*first == n*(4*z2+(1<<(2*n)))
        second = sum(k*k*row[k]*(1<<k) for k in range(1,n+1))
        central = math.comb(2*n,n)
        assert 30*second == (4*(4*n**3+23*n*n+63*n+30)*central
                             -15*(n+2)*(n+4)*(1<<(2*n)))
        # Polynomial factorization and column recurrence.
        for k in range(2,n):
            fall = lambda a,r: math.prod(range(a-r+1,a+1))
            h = (1<<(k-1))*fall(n,k-1)-fall(2*n-k-1,k-1)
            assert h > 0
            assert row[k]*math.factorial(n-k-1)*math.factorial(n) == math.factorial(2*n-2*k)*h
            hn = (1<<(k-1))*fall(n+1,k-1)-fall(2*n-k+1,k-1)
            assert (n-k)*(n+1)*h*entry(n+1,k) == 2*(n-k+1)*(2*n-2*k+1)*hn*row[k]
        if n >= 3:
            for k in range(2,n+1):
                rhs = (3*entry(n-1,k-1)-2*entry(n-2,k-2)
                       +entry(n,k+1)-2*entry(n-1,k)
                       +(catalan(n-2) if k == 2 else 0))
                assert row[k] == rhs
        entries += n
        if n == max_n:
            break
        # Suffix sums implement all transitions d -> 1,...,d+1 in O(n^2).
        nxt: dict[tuple[int,int], int] = {}
        for k in range(1,n):
            running = 0
            for j in range(n+1,1,-1):
                running += states.get((j-1,k),0)
                if running:
                    nxt[(j,k)] = running
            if running:
                nxt[(1,k)] = running
        # Safe insertion sites: append (j=0), or before last (j=1).
        # Every other active site is the first violation, with K=n.
        safe = [states.get((d,0),0) for d in range(n+2)]
        for d in range(1,n+1):
            v=safe[d]
            if not v:
                continue
            nxt[(d+1,0)] = nxt.get((d+1,0),0)+v
            nxt[(1,0)] = nxt.get((1,0),0)+v
        running = 0
        for j in range(n,1,-1):
            running += safe[j]
            if running:
                nxt[(j,n)] = running
        states = nxt
    return entries

def symbolic_checks() -> dict[str,str]:
    z,y,k,r = sp.symbols('z y k r')
    x=(1-z*z)/4
    c=2/(1+z)
    f=x*y/(1-2*x*y)+x**3*y**2*c**3/((1-2*x*y)*(1-x*y*c))
    conjecture=c-1+(1-y)*(1-x*y)*(1-(1-x*y)*c)/((1-2*x*y)*(1-y+x*y*y))
    assert sp.factor(f-conjecture) == 0
    assert sp.factor(f.subs(y,1)-(c-1)) == 0
    critical=-1+sp.Rational(3,2)/z-1/z**2+sp.Rational(1,2)/z**3
    assert sp.factor(f.subs(y,2)-critical) == 0
    p=y*y*(3-y)/(2*(2-y)**3)
    assert sp.factor(-sp.diff(f,z).subs(z,0)/2-p) == 0
    assert sp.diff(p,y).subs(y,1) == sp.Rational(9,2)
    assert (sp.diff(p,y,2)+sp.diff(p,y)).subs(y,1)-sp.Rational(9,2)**2 == sp.Rational(21,4)
    aa,bb={},{}
    for m in range(1,5):
        sm=lambda b: sp.summation(r**m,(r,0,b))
        aa[m]=sp.factor((sp.Rational(1,2)**m*sm(2*k-1)-sm(k)-sm(k-2))/m)
        bb[m]=sp.factor((sp.Rational(1,2)**m-1)*sm(k)/m)
    def exp_coeff(logc):
        e=[sp.Integer(1)]
        for j in range(1,5):
            e.append(sp.factor(sum(m*logc[m]*e[j-m] for m in range(1,j+1))/j))
        return e
    ea,eb=exp_coeff(aa),exp_coeff(bb)
    d=[sp.factor(ea[j]-eb[j]) for j in range(1,5)]
    assert sp.factor(d[0]-(k-1)*(k+4)/4) == 0
    pr=[sp.Integer(1)]+[sp.factor((d[j]+d[j-1])/d[0]) for j in range(1,4)]
    cat=[sp.Integer(1),-sp.Rational(9,8),sp.Rational(145,128),-sp.Rational(1155,1024)]
    co=[sp.factor(sum(pr[j]*cat[i-j] for j in range(i+1))) for i in range(1,4)]
    c1=-(k**3-k**2-17*k+36)/(8*(k+4))
    c2=(4*k**5-32*k**4-22*k**3+578*k**2-2601*k+1740)/(384*(k+4))
    assert sp.factor(co[0]-c1)==0 and sp.factor(co[1]-c2)==0
    return {'c1':str(co[0]),'c2':str(co[1]),'c3':str(co[2]),
            'probability_c1':str(pr[1]),'probability_c2':str(pr[2])}

def leading_probability(k: int) -> mp.mpf:
    return mp.mpf((k-1)*(k+4))/mp.power(2,k+3)

def correction_coefficients(k: int) -> tuple[mp.mpf,mp.mpf]:
    c1=-mp.mpf(k**3-k*k-17*k+36)/(8*(k+4))
    c2=mp.mpf(4*k**5-32*k**4-22*k**3+578*k*k-2601*k+1740)/(384*(k+4))
    return c1,c2

def smooth_log_entry(x: mp.mpf,k: int) -> mp.mpf:
    if x <= k:
        raise ValueError('The smooth interpolation requires x>k.')
    ell=x-k
    loga=(k-1)*mp.log(2)+mp.loggamma(2*ell+1)-mp.loggamma(ell)-mp.loggamma(ell+2)
    logr=mp.fsum(mp.log1p(mp.mpf(j)/(2*ell))-mp.log1p(mp.mpf(j+1)/ell) for j in range(1,k))
    return loga+mp.log(-mp.expm1(logr))

def inverse_approx(log_target: mp.mpf,k: int) -> tuple[mp.mpf,mp.mpf,mp.mpf]:
    a,b=mp.log(4),mp.mpf('1.5')
    pref=leading_probability(k)/mp.sqrt(mp.pi)
    Y=log_target-mp.log(pref)
    N=-b/a*mp.lambertw(-a/b*mp.exp(-Y/b),-1).real
    c1,c2=correction_coefficients(k)
    l2=c2-c1*c1/2
    return N,N-c1/(a*N),N-c1/(a*N)-(l2/a+b*c1/a**2)/N**2

def write_csv(name: str,headers: list[str],rows: list[list[object]]) -> None:
    with (ROOT/'data'/name).open('w',newline='') as out:
        w=csv.writer(out);w.writerow(headers);w.writerows(rows)

def numerical_checks() -> dict:
    mp.mp.dps=100
    fmt=lambda x:mp.nstr(x,18)
    rows=[]
    for k in (2,3,5,8):
        c1,c2=correction_coefficients(k)
        pref=leading_probability(k)/mp.sqrt(mp.pi)
        for n in (20,100,500):
            exact=mp.mpf(entry(n,k))
            lead=pref*mp.power(4,n)/mp.power(n,mp.mpf('1.5'))
            rel=[lead/exact-1,lead*(1+c1/n)/exact-1,lead*(1+c1/n+c2/n**2)/exact-1]
            rows.append([k,n,*map(fmt,rel)])
    write_csv('fixed_column_errors.csv',['k','n','leading_relative_error','one_correction_error','two_corrections_error'],rows)
    rows=[]
    for n in (20,50,100,200,500,1000):
        z=(n+2)*math.comb(2*n,n)-(1<<(2*n))
        weighted=[entry(n,k)*(1<<k) for k in range(1,n+1)]
        assert sum(weighted)==z
        mean=mp.mpf(sum(k*v for k,v in enumerate(weighted,1)))/z/n
        cdf=mp.mpf(sum(weighted[:n//2]))/z
        rows.append([n,fmt(mean),fmt(mean-mp.mpf(2)/3),fmt(cdf),fmt(cdf-(1-1/mp.sqrt(2)))])
    write_csv('critical_limit.csv',['n','E_K_over_n','error_to_2_over_3','cdf_at_one_half','cdf_error'],rows)
    rows=[]
    for n in (100,400,1600,6400):
        for sv in (mp.mpf('0.5'),mp.mpf(1),mp.mpf(2)):
            k=int(mp.floor(sv*mp.sqrt(n)))
            exact=mp.mpf(entry(n,k))
            pred=mp.power(4,n)*mp.power(2,-k)/(2*mp.sqrt(mp.pi*n))*(-mp.expm1(-mp.mpf(k*k)/(4*n)))
            rows.append([n,k,fmt(mp.mpf(k)/mp.sqrt(n)),fmt(exact/pred)])
    write_csv('crossover.csv',['n','k','k_over_sqrt_n','exact_over_crossover'],rows)
    rows=[]
    for k in (2,3,5):
        for target_x in (mp.mpf('30.25'),mp.mpf('100.25'),mp.mpf('300.25')):
            logt=smooth_log_entry(target_x,k)
            appr=inverse_approx(logt,k)
            rows.append([k,fmt(target_x),*[fmt(v-target_x) for v in appr]])
    write_csv('inverse_errors.csv',['k','true_x','Lambert_error','first_correction_error','second_correction_error'],rows)
    # Fixed-deficit exponential limiting law.
    y=mp.mpf(3); q=mp.sqrt(1-2/y); amplitude=(q*q+1)/(2*q*(q+1))
    rows=[]
    for n in (20,50,100):
        weights=[mp.mpf(entry(n,k))*mp.power(y,k) for k in range(1,n+1)]
        zn=mp.fsum(weights)
        for ell in range(4):
            predicted=(mp.mpf('0.5') if ell==0 else mp.mpf(math.comb(2*ell,ell-1))/(2*mp.power(2*y,ell)))/amplitude
            rows.append([n,ell,fmt(weights[n-ell-1]/zn),fmt(predicted)])
    write_csv('supercritical.csv',['n','deficit','actual_probability','limit_probability'],rows)
    return {'fixed_column_rows':12,'critical_rows':6,'crossover_rows':12,'inverse_rows':9,'supercritical_rows':12}

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--brute-max',type=int,default=9)
    parser.add_argument('--dp-max',type=int,default=120)
    args=parser.parse_args()
    if not 1<=args.brute_max<=10 or not 2<=args.dp_max<=400:
        parser.error('Use 1<=brute-max<=10 and 2<=dp-max<=400.')
    (ROOT/'data').mkdir(exist_ok=True)
    tested=brute_checks(args.brute_max)
    cells=insertion_checks(args.dp_max)
    symbolic=symbolic_checks()
    numerical=numerical_checks()
    out={'status':'all checks passed','brute_max':args.brute_max,'permutations_tested':tested,
         'insertion_max':args.dp_max,'triangle_cells_tested':cells,
         'symbolic_coefficients':symbolic,'numerical_tables':numerical}
    (ROOT/'data'/'verification_summary.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':
    main()
