#!/usr/bin/env python3
"""Independent exact and high-precision checks for the accompanying article.

Python >= 3.10; mpmath is the only non-standard dependency.  Numerical checks
are diagnostic, NOT interval certificates or formal proofs.  Exact checks use
fractions.Fraction.  Run from any working directory; outputs go to ../data.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json
import mpmath as mp

COUNTS: Counter[str] = Counter()

def det_exact(rows):
    n = len(rows)
    if not n:
        return F(1)
    a = [[F(x) for x in row] for row in rows]
    ans = F(1)
    for j in range(n):
        p = next((i for i in range(j, n) if a[i][j]), None)
        if p is None:
            return F(0)
        if p != j:
            a[j], a[p] = a[p], a[j]
            ans = -ans
        v = a[j][j]
        ans *= v
        for i in range(j + 1, n):
            c = a[i][j] / v
            for k in range(j + 1, n):
                a[i][k] -= c * a[j][k]
    return ans

def groups(xs):
    out = []
    for x in xs:
        for item in out:
            if item[0] == x:
                item[1] += 1
                break
        else:
            out.append([x, 1])
    return out

def poly_roots(xs):
    p = [F(1)]
    for x in xs:
        q = [F(0)] * (len(p) + 1)
        for j, a in enumerate(p):
            q[j] -= x * a
            q[j + 1] += a
        p = q
    return p

def catalan(n):
    return comb(2*n, n) // (n + 1)

def direct_hankel(n, roots):
    p = poly_roots(roots)
    return det_exact([[sum(a*catalan(i+j+k) for k,a in enumerate(p))
                       for j in range(n)] for i in range(n)])

def polynomial_jets(c, multiplicity, last):
    """Normalized Taylor jets of the Catalan monic orthogonal polynomials."""
    p0 = [c*0 + 1] + [c*0]*(multiplicity-1)
    out = [p0]
    if last == 0:
        return out
    p1 = [c-1] + ([c*0 + 1] if multiplicity > 1 else [])
    p1 += [c*0] * (multiplicity-len(p1))
    out.append(p1)
    for _ in range(1, last):
        p2 = [(c-2)*p1[r] - p0[r] + (p1[r-1] if r else 0)
              for r in range(multiplicity)]
        out.append(p2)
        p0, p1 = p1, p2
    return out

def christoffel(n, roots, exact=False):
    d = len(roots)
    if not d:
        return F(1) if exact else mp.mpf(1)
    gs = groups(roots)
    mat = []
    den = 1
    for i, (c, k) in enumerate(gs):
        jets = polynomial_jets(c, k, n+d-1)
        mat += [[jets[n+j][r] for j in range(d)] for r in range(k)]
        for b, t in gs[i+1:]:
            den *= (b-c)**(k*t)
    val = det_exact(mat) if exact else mp.det(mp.matrix(mat))
    return (-1)**(n*d) * val / den

def exact_tests():
    patterns = [[], [0], [4], [0,0], [4,4], [0,4], [0,0,4],
                [0,4,4], [0,0,4,4], [1,1,3], [-1,2,5],
                [F(1,2),F(1,2),F(9,2)], [2,2,2,2]]
    for xs in patterns:
        xs = list(map(F, xs))
        for n in range(0,8):
            assert direct_hankel(n,xs) == christoffel(n,xs,True)
            COUNTS['exact_original_vs_confluent_Christoffel'] += 1
    for n in range(0,21):
        for r in range(0,9):
            j0 = polynomial_jets(F(0),9,n)[n][r]
            j4 = polynomial_jets(F(4),9,n)[n][r]
            b = comb(n+r,2*r) if n >= r else 0
            assert j0 == (-1)**(n+r)*b
            assert j4 == F(2*n+1,2*r+1)*b
            COUNTS['exact_endpoint_jets'] += 2
    for m in range(0,6):
        for l in range(0,6):
            d=m+l
            if not d:
                continue
            aa=[F(2*j-d+1,2) for j in range(d)]
            r=list(range(m)); s=list(range(l))
            def vdet(r,s):
                rows=[[(-1)**j*aa[j]**k/factorial(k) for j in range(d)] for k in r]
                rows += [[aa[j]**k/factorial(k) for j in range(d)] for k in s]
                return det_exact(rows)
            base=vdet(r,s)
            assert base == (-1)**(m*(m-1)//2)*2**(m*l)
            COUNTS['exact_centered_minor_constants'] += 1
            for side,n,other in [(0,m,l),(1,l,m)]:
                if n:
                    r1=list(range(n-1))+[n]
                    v=vdet(r1,s) if side==0 else vdet(r,r1)
                    assert v == 0
                    COUNTS['exact_odd_minor_vanishing'] += 1
                    r2=list(range(n-1))+[n+1]
                    v=vdet(r2,s) if side==0 else vdet(r,r2)
                    assert v/base == F(n+3*other-1,24)
                    COUNTS['exact_second_order_minors'] += 1
                if n >= 2:
                    r11=list(range(n-2))+[n-1,n]
                    v=vdet(r11,s) if side==0 else vdet(r,r11)
                    assert v/base == -F(n+3*other+1,24)
                    COUNTS['exact_second_order_minors'] += 1
            if m and l:
                v=vdet(list(range(m-1))+[m],list(range(l-1))+[l])
                assert v/base == -F(1,4)
                COUNTS['exact_mixed_minor'] += 1


def fjet(epsilon, r, q, t, y):
    """(1/q!) d_y^q d_t^r [cos(t sqrt(y)) or sin(t sqrt(y))/sqrt(y)]."""
    k0=max(q,(r-epsilon+1)//2,0)
    ans=mp.mpc(0); tiny=0
    for k in range(k0,600):
        power=2*k+epsilon-r
        term=((-1)**k * comb(k,q) * y**(k-q) * t**power
              / mp.factorial(power))
        ans += term
        if abs(term) < mp.eps*max(1,abs(ans)):
            tiny += 1
            if tiny >= 8:
                return ans
        else:
            tiny=0
    raise ArithmeticError('Entire jet series did not converge within 600 terms')

def kernel(epsilon, xs, indices=None, t=1):
    n=len(xs)
    if n==0:
        return mp.mpf(1)
    if indices is None:
        indices=list(range(n))
    gs=groups(xs); mat=[]; den=mp.mpf(1)
    for i,(y,k) in enumerate(gs):
        mat += [[fjet(epsilon,r,q,t,y) for r in indices] for q in range(k)]
        for z,v in gs[i+1:]:
            den *= (z-y)**(k*v)
    return (-1)**(n*(n-1)//2)*mp.det(mp.matrix(mat))/den

def kernel012(epsilon, xs):
    n=len(xs)
    if not n:
        return mp.mpf(1),mp.mpf(0),mp.mpf(0)
    k0=kernel(epsilon,xs)
    k1=kernel(epsilon,xs,list(range(n-1))+[n])
    k2=kernel(epsilon,xs,list(range(n-1))+[n+1])
    if n >= 2:
        k2 += kernel(epsilon,xs,list(range(n-2))+[n-1,n])
    return k0,k1,k2

def coeff01(ys, vs):
    m=len(ys); l=len(vs)
    a,a1,a2=kernel012(0,ys); b,b1,b2=kernel012(1,vs)
    pref=mp.mpf(2)**(l-m*l)
    potential=((m+3*l+1)*sum(ys)+(l+3*m-1)*sum(vs))/24
    return pref*a*b,pref*(potential*a*b-(a2*b+a*b2)/24-a1*b1/4)

def normalized_hankel(n, ys, vs):
    m=len(ys); l=len(vs); nu=mp.mpf(n)+mp.mpf(m+l)/2
    h=1/nu; kap=m*(m-1)//2+l*(l+1)//2
    # sin^2 is more stable than 2-2*cos for small h.
    left=[4*mp.sin(h*mp.sqrt(y)/2)**2 for y in ys]
    right=[4-4*mp.sin(h*mp.sqrt(v)/2)**2 for v in vs]
    return (-1)**(n*l)*christoffel(n,left+right)/nu**kap

def analytic_z(h,ys,vs):
    """Exact analytic continuation used for evenness checks; distinct nodes only."""
    m=len(ys);l=len(vs);d=m+l
    q=m*(m-1)//2+l*(l-1)//2
    aa=[mp.mpf(2*j-d+1)/2 for j in range(d)]
    M=[]
    for y in ys:
        M.append([(-1)**j*mp.cos((1+a*h)*mp.sqrt(y)) for j,a in enumerate(aa)])
    for v in vs:
        M.append([fjet(1,0,0,1+a*h,v) for a in aa])
    phi=lambda y: 4*mp.sin(h*mp.sqrt(y)/2)**2/h**2
    den=mp.mpf(1)
    for y in ys:
        den*=mp.cos(h*mp.sqrt(y)/2)
    for v in vs:
        w=h*mp.sqrt(v)/2
        den*=mp.sin(w)/w if w else 1
    for xs in [ys,vs]:
        for i,x in enumerate(xs):
            for y in xs[i+1:]: den*=phi(y)-phi(x)
    for y in ys:
        for v in vs: den*=4-h*h*(phi(y)+phi(v))
    return 2**l*(-1)**(l*(l-1)//2)*mp.det(mp.matrix(M))/(h**q*den)

def number(z,digits=25):
    z=mp.chop(z)
    return mp.nstr(z,digits)

def numeric_tests():
    mp.mp.dps=100
    cases=[('left-one',[-1],[]),('right-one',[],[-1]),
           ('one-at-each',[-1],[-2]),('left-double',[-1,-1],[]),
           ('right-double',[],[-1,-1]),('both-double',[-1,-1],[-2,-2]),
           ('endpoint-double',[0,0],[0,0]),('three-plus-two',[-1,-1,0],[-2,0]),
           ('inside-collisions',[1,1],[2,2]),
           ('complex-distinct',[mp.mpc(1,1),mp.mpc(-2,.5)],[-1,2])]
    result=[]
    for name,ys,vs in cases:
        ys=list(map(mp.mpc,ys));vs=list(map(mp.mpc,vs))
        a0,a1=coeff01(ys,vs); rows=[]
        for n in [16,32,64,128]:
            h=1/(mp.mpf(n)+mp.mpf(len(ys)+len(vs))/2)
            z=normalized_hankel(n,ys,vs)
            e0=z-a0;e1=z-a0-h*h*a1
            rows.append({'N':n,'Z':number(z),'A0':number(a0),'A1':number(a1),
                         'abs_leading_error':number(abs(e0)),
                         'abs_corrected_error':number(abs(e1)),
                         'leading_error_over_h2':number(e0/h**2),
                         'corrected_error_over_h4':number(e1/h**4)})
            # A loose analytic diagnostic, not a proof of the asymptotics.
            assert abs(e1) < 50*h**4*max(1,abs(a0),abs(a1))
            COUNTS['high_precision_second_order_checks'] += 1
        result.append({'case':name,'left':list(map(number,ys)),
                       'right':list(map(number,vs)),'rows':rows})
    for m,l in [(1,0),(0,1),(2,1),(1,3),(3,2),(2,3)]:
        ys=[mp.mpf(i+1)/3 for i in range(m)]
        vs=[-mp.mpf(i+1)/5 for i in range(l)]
        h=mp.mpc('0.031','0.002')
        zp=analytic_z(h,ys,vs); zm=analytic_z(-h,ys,vs)
        assert abs(zp-zm)<mp.mpf('1e-75')*max(1,abs(zp))
        COUNTS['high_precision_evenness'] += 1
        n=20; hn=1/(mp.mpf(n)+mp.mpf(m+l)/2)
        aa=analytic_z(hn,ys,vs); bb=normalized_hankel(n,ys,vs)
        assert abs(aa-bb)<mp.mpf('1e-75')*max(1,abs(aa))
        COUNTS['analytic_vs_Christoffel'] += 1
    for m in range(0,5):
        for l in range(0,5):
            if not m+l: continue
            kap0=m*(m-1)//2;kap1=l*(l+1)//2
            a0,a1=coeff01([mp.mpf(0)]*m,[mp.mpf(0)]*l)
            exact=F(2)**(l-m*l+m*(m-1)//2+l*(l-1)//2)
            for j in range(m): exact*=F(factorial(j),factorial(2*j))
            for j in range(l): exact*=F(factorial(j),factorial(2*j+1))
            assert abs(a0-mp.mpf(exact.numerator)/exact.denominator)<mp.mpf('1e-80')
            second=-F(kap0*(kap0-1)+kap1*(kap1-1)+6*kap0*kap1,24)
            assert abs(a1/a0-mp.mpf(second.numerator)/second.denominator)<mp.mpf('1e-80')
            COUNTS['endpoint_coefficient_checks'] += 2
    return result

def main():
    exact_tests()
    results=numeric_tests()
    data=Path(__file__).resolve().parents[1]/'data'; data.mkdir(exist_ok=True)
    record={'precision_decimal_digits':mp.mp.dps,'counts':dict(COUNTS),
            'total':sum(COUNTS.values()),'all_passed':True,
            'qualification':'Numerical checks are not outward-rounded interval certificates.',
            'cases':results}
    (data/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    lines=['All checks passed.']+[f'{k}: {v}' for k,v in COUNTS.items()]
    lines += [f'TOTAL: {sum(COUNTS.values())}',
              'Exact arithmetic and diagnostic high precision are distinguished in verification.json.']
    (data/'verification.txt').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__': main()
