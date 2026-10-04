#!/usr/bin/env python3
"""Exact algebra and high-precision checks for Complex Transseries at q-Cusps.

No network access is used. Numerical checks are not interval certificates.
Run from any directory; output goes to ../data/verification.json.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import gcd, lcm
import json, platform
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]

def divisors(n: int) -> list[int]:
    return [d for d in range(1, n+1) if n % d == 0]

def mobius(n: int) -> int:
    s, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p; s = -s
            if n % p == 0: return 0
            while n % p == 0: n //= p
        p += 1
    return -s if n > 1 else s

def sigma1(n: int) -> int:
    return sum(divisors(n))

def jordan2(n: int) -> int:
    return sum(mobius(n//d)*d*d for d in divisors(n))

def mul(a: list[F], b: list[F], n: int) -> list[F]:
    ans = [F(0)]*(n+1)
    for i, x in enumerate(a[:n+1]):
        for j, y in enumerate(b[:n+1-i]): ans[i+j] += x*y
    return ans

def power(a: list[F], p: F, n: int) -> list[F]:
    """Taylor coefficients of a**p, with a[0] == 1, exactly."""
    if not a or a[0] != 1: raise ValueError('Unit series required')
    a = a[:n+1] + [F(0)]*max(0,n+1-len(a))
    b = [F(1)]
    for j in range(1,n+1):
        b.append(sum((((p+1)*k-j)*a[k]*b[j-k] for k in range(1,j+1)),F(0))/j)
    return b

def compose(a: list[F], b: list[F], n: int) -> list[F]:
    if b[0] != 0: raise ValueError('Inner constant must vanish')
    ans = [F(0)]*(n+1); bp = [F(1)]+[F(0)]*n
    for x in a[:n+1]:
        ans = [u+x*v for u,v in zip(ans,bp)]
        bp = mul(bp,b,n)
    return ans

def euler_quotient_series(r: dict[int,int], n: int) -> list[F]:
    """Coefficients of product_d (Q**d;Q**d)_infinity**r[d]."""
    ell = [F(0)] + [-F(sum(v*d*sigma1(j//d) for d,v in r.items() if j%d == 0),j)
                         for j in range(1,n+1)]
    h = [F(1)]
    for j in range(1,n+1):
        h.append(sum((k*ell[k]*h[j-k] for k in range(1,j+1)),F(0))/j)
    return h

def inverse_flat(h: list[F], m: int, n: int) -> list[F]:
    """Q(s) for 1-H(Q)=s**m, assuming leading coefficient of 1-H is 1."""
    if any(h[j] for j in range(1,m)) or h[m] != -1:
        raise ValueError('Wrong flat normalization')
    b = [-x for x in h[m:]]
    return [F(0)]+[power(b,-F(j,m),j-1)[j-1]/j for j in range(1,n+1)]

def log_unit(a: list[F], n: int) -> list[F]:
    inv = power(a,F(-1),n)
    der = [(i+1)*a[i+1] for i in range(min(n,len(a)-1))]
    prod = mul(der,inv,n-1)
    return [F(0)]+[prod[j-1]/j for j in range(1,n+1)]

def cusp_data(r: dict[int,int], N: int) -> dict[int,F]:
    return {k:sum((F(v*gcd(k,d)**2,d) for d,v in r.items()),F(0)) for k in divisors(N)}

def recover(a: dict[int,F], N: int) -> dict[int,F]:
    b = {j:sum((mobius(j//e)*a[e] for e in divisors(j)),F(0))/jordan2(j)
         for j in divisors(N)}
    return {d:d*sum((mobius(j//d)*b[j] for j in divisors(N) if j%d == 0),F(0))
            for d in divisors(N)}

def dedekind(d: int, c: int) -> F:
    if c == 1: return F(0)
    return sum(((F(n,c)-F(1,2))*(F((d*n)%c,c)-F(1,2)) for n in range(1,c)),F(0))

def mpf(x: F | int):
    if isinstance(x,F): return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(x)

def poch(q, digits: int = 105):
    """Direct product via log1p. Tail bound is included in the article."""
    q = mp.mpc(q); r = abs(q)
    if not r < 1: raise ValueError('Requires |q| < 1')
    if r == 0: return mp.mpc(1)
    tol = mp.power(10,-digits)
    n = max(1, int(mp.ceil(mp.log(tol*(1-r)**2)/mp.log(r))))
    z = q; logs = mp.mpc(0)
    for _ in range(n):
        logs += mp.log1p(-z); z *= q
    return mp.exp(logs)

def quotient(q, r: dict[int,int]):
    ans = mp.mpc(1)
    for d,v in r.items(): ans *= poch(q**d)**v
    return ans

def transformed(t, h: int, k: int, r: dict[int,int], N: int):
    R = sum(r.values()); B = sum(d*v for d,v in r.items())/mp.mpf(24)
    ak = sum((F(v*gcd(k,d)**2,d) for d,v in r.items()),F(0))
    A = mp.pi**2*mpf(ak)/(6*k*k)
    C = (2*mp.pi)**(mp.mpf(R)/2); H = mp.mpc(1)
    action = 4*mp.pi**2/(k*k*N); Q = mp.exp(-action/t)
    for delta,v in r.items():
        g = gcd(k,delta); c = k//g; a = delta*h//g
        dinv = pow(a,-1,c) if c > 1 else 0
        phase = mp.exp(-mp.pi*1j*mpf(dedekind(dinv,c)))
        C *= phase**v * mp.mpf(c*delta)**(-mp.mpf(v)/2)
        rho = mp.exp(-2*mp.pi*1j*dinv/c)
        m = N*g*g//delta
        H *= poch(rho*Q**m)**v
    return C*t**(-mp.mpf(R)/2)*mp.exp(-A/t+B*t)*H

def evalpoly(a: list[F], x):
    y = mp.mpc(0)
    for c in reversed(a): y = y*x + mpf(c)
    return y

def exact_checks():
    count = 0; output = {}
    for name,rs,m in [('level6',{1:-1,2:5,3:-5,6:1},1),
                       ('level12',{2:-1,3:4,4:-4,6:1},2)]:
        N = lcm(*rs)
        assert sum(rs.values()) == 0
        assert sum(d*v for d,v in rs.items()) == 0
        assert sum((F(v,d) for d,v in rs.items()),F(0)) == 0
        count += 3
        h = euler_quotient_series({N//d:v for d,v in rs.items()},24)
        inv = inverse_flat(h,m,12)
        comp = compose([F(0)]+[-x for x in h[1:]],inv,12)
        for j in range(13):
            assert comp[j] == int(j==m), (name,j,comp[j]); count += 1
        logs = log_unit(inv[1:],10)
        a = cusp_data(rs,N); rec = recover(a,N)
        for d in divisors(N): assert rec[d] == rs.get(d,0); count += 1
        output[name] = {'r':rs,'H':[str(c) for c in h[:13]],
                        'Q_inverse':[str(c) for c in inv[:11]],
                        'log_Q_over_s':[str(c) for c in logs[:9]],
                        'cusp_a':{str(k):str(v) for k,v in a.items()}}
    # Test the exact cusp recovery matrix on every coordinate vector.
    for N in [1,2,6,12,24,30,60]:
        for e in divisors(N):
            a = cusp_data({e:1},N); rec = recover(a,N)
            for d in divisors(N): assert rec[d] == int(e==d); count += 1
    # Four-node Vandermonde kernel, independently tested.
    for ds in [[1,2,3,6],[2,3,4,6],[1,3,5,8]]:
        vec=[]
        for d in ds:
            den=1
            for e in ds:
                if e != d: den*=d-e
            vec.append(F(d,den))
        for p in [-1,0,1]:
            assert sum((v*F(d)**p for d,v in zip(ds,vec)),F(0)) == 0; count += 1
    # Every finite correction degree is realized with four active scales.
    degrees = {}
    for degree in range(1,31):
        ds = ([1,2,3,6] if degree == 1 else
              [2,3,4,6] if degree == 2 else [1,2,degree,degree+1])
        N = lcm(*ds)
        assert len(set(ds)) == 4; count += 1
        assert N//max(ds) == degree; count += 1
        assert gcd(*(N//d for d in ds)) == 1; count += 1
        vec = []
        for d in ds:
            den = 1
            for e in ds:
                if e != d: den *= d-e
            vec.append(F(d,den))
        assert all(vec); count += 1
        for exponent in [-1,0,1]:
            assert sum((v*F(d)**exponent for d,v in zip(ds,vec)),F(0)) == 0
            count += 1
        degrees[str(degree)] = {'scales':ds,'level':N,
                                'rational_kernel':[str(v) for v in vec]}
    output['ramification_construction'] = degrees
    # Independent exact residual checks of t=u(A+b1*t**2+b2*t**4).
    for A,b1,b2 in [(F(2),F(1,3),F(-2,7)),
                    (F(3,2),F(-3,5),F(4,9)),
                    (F(5,7),F(2,11),F(-1,13))]:
        t = [F(0),A,F(0),b1*A*A,F(0),2*b1*b1*A**3+b2*A**4]
        t2 = mul(t,t,4); t4 = mul(t2,t2,4)
        rhs = [b1*x+b2*y for x,y in zip(t2,t4)]
        rhs[0] += A
        for j in range(5): assert t[j+1] == rhs[j]; count += 1
    # Finite Gaussian multinomial and its exact quadratic cusp coefficient.
    phi3 = [F(1),F(1),F(1)]
    phi4 = [F(1),F(0),F(1)]
    phi5 = [F(1)]*5
    phi6 = [F(1),F(-1),F(1)]
    finite = [F(1)]+[F(0)]*12
    for j in range(1,7):
        factor = [F(1)]+[F(0)]*(j-1)+[F(-1)]
        finite = mul(finite,power(factor,F(-2 if j<=2 else 1),12),12)
    cyclo = mul(mul(mul(mul(phi3,phi3,12),phi4,12),phi5,12),phi6,12)
    for j in range(13): assert finite[j] == cyclo[j]; count += 1
    local = mul(mul(mul([F(1),F(4),F(4)],phi4,10),phi5,10),phi6,10)
    for j in range(len(local)-1,1,-1):
        c = local[j]; local[j]=F(0)
        local[j-1] -= c; local[j-2] -= c
    assert local[:2] == [F(0),F(6)]; count += 1
    output['finite_multinomial'] = [str(c) for c in finite]
    output['assertion_count'] = count
    return output

def numeric_checks(exact):
    mp.mp.dps = 115
    rs={1:-1,2:5,3:-5,6:1}; rs2={2:-1,3:4,4:-4,6:1}
    tests=[]
    for r,N in [(rs,6),(rs2,12),({1:2,2:-1,3:1},6)]:
        for h,k in [(0,1),(1,2),(1,3),(2,5),(1,6)]:
            t=mp.mpc('0.37','0.09')
            q=mp.exp(2*mp.pi*1j*h/k-t)
            direct=quotient(q,r); dual=transformed(t,h,k,r,N)
            rel=abs(direct/dual-1)
            assert rel < mp.mpf('1e-90'), (r,h,k,rel)
            tests.append({'r':r,'h':h,'k':k,'relative_error':mp.nstr(rel,10)})
    inverse_tests=[]
    for t in [mp.mpc('0.5'),mp.mpc('0.35'),mp.mpc('0.25'),mp.mpc('0.4','0.08')]:
        y=mp.mpf(8)/9*quotient(mp.exp(-t),rs); u=1-y
        action=2*mp.pi**2/3
        inv=[F(x) for x in exact['level6']['Q_inverse']]
        deck=int(mp.nint((mp.im(-action/t)-mp.arg(u))/(2*mp.pi)))
        row={'t':str(t),'abs_u':mp.nstr(abs(u),12),'log_deck':deck,'errors':{}}
        for n in [1,2,4,8]:
            Qn=evalpoly(inv[:n+1],u)
            tn=-action/(mp.log(Qn)+2*mp.pi*1j*deck)
            err=abs(tn-t)
            row['errors'][str(n)]=mp.nstr(err,12)
        assert mp.mpf(row['errors']['8']) < mp.mpf('1e-39')
        assert mp.mpf(row['errors']['8']) < mp.mpf(row['errors']['1'])
        inverse_tests.append(row)
    # Two genuine square-root branches, checked in the dual analytic germ.
    h2=[F(x) for x in exact['level12']['H']]
    inv2=[F(x) for x in exact['level12']['Q_inverse']]
    branch=[]
    for s in [mp.mpf('0.00001'),-mp.mpf('0.00001')]:
        Q=evalpoly(inv2,s)
        H=quotient(Q,{12//d:v for d,v in rs2.items()})
        residual=abs(1-H-s*s)
        assert residual < mp.mpf('1e-46')
        branch.append({'s':mp.nstr(s,10),'Q':mp.nstr(Q,24),'residual':mp.nstr(residual,12)})
    return {'precision_digits':mp.mp.dps,'modular_checks':tests,
            'inverse_checks':inverse_tests,'ramified_checks':branch,
            'status':'All numerical assertions passed; not interval certified.'}

def main():
    exact=exact_checks(); numerical=numeric_checks(exact)
    data={'python':platform.python_version(),'mpmath':mp.__version__,
          'exact':exact,'numerical':numerical}
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'verification.json').write_text(json.dumps(data,indent=2)+'\n', encoding='utf-8', newline='\n')
    print('Exact assertions:',exact['assertion_count'])
    print('Modular identity tests:',len(numerical['modular_checks']))
    for name in ['level6','level12']:
        print(name,'H=',exact[name]['H'])
        print(name,'Q inverse=',exact[name]['Q_inverse'])
        print(name,'log=',exact[name]['log_Q_over_s'])
    for row in numerical['inverse_checks']: print(row)
    print(numerical['status'])

if __name__=='__main__': main()
