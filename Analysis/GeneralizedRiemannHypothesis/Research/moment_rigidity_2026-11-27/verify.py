#!/usr/bin/env python3
"""Standard-library arithmetic checks; no tests are used in the general proof."""
from math import comb, factorial, gcd, prod
from itertools import combinations_with_replacement


def isprime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**.5)+1))


def block(p, s):
    # Take one square root of each member of the order-s subgroup of squares.
    assert (p-1) % (2*s) == 0
    roots = [a for a in range(1, (p+1)//2) if pow(a, 2*s, p) == 1]
    assert len(roots) == s
    return roots


def moments(p, steps):
    out = []
    for a,b in [(1,j) for j in range(p)] + [(0,1)]:
        vals = [(a*x+b*y)**2 % p for x,y in steps]
        out.append(next(j for j in range(1,len(steps)+1)
                        if sum(pow(v,j,p) for v in vals) % p))
    return out


def bareiss(a):
    a = [r[:] for r in a]
    n = len(a); prev = 1; sign = 1
    for k in range(n-1):
        if not a[k][k]:
            r = next((r for r in range(k+1,n) if a[r][k]), None)
            if r is None: return 0
            a[k], a[r] = a[r], a[k]; sign = -sign
        pivot = a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                num = pivot*a[i][j] - a[i][k]*a[k][j]
                assert num % prev == 0
                a[i][j] = num // prev
            a[i][k] = 0
        prev = pivot
    return sign*a[-1][-1]


def vp(n,p):
    assert n != 0
    n = abs(n); k = 0
    while n % p == 0: n //= p; k += 1
    return k


def cyclotomic_norm(p, steps, a,b):
    # Exact multiplication matrix of Laplacian value in Z[Z]/Phi_p.
    c = [0]*p; c[0] = 2*len(steps)
    for x,y in steps:
        r = (a*x+b*y)%p
        c[r] -= 1; c[-r % p] -= 1
    mat = [[c[(i-j)%p]-c[(p-1-j)%p] for j in range(p-1)]
           for i in range(p-1)]
    return bareiss(mat)


def graph_check(p,steps):
    ds = moments(p,steps)
    ns = [vp(cyclotomic_norm(p,steps,a,b),p)
          for a,b in [(1,j) for j in range(p)] + [(0,1)]]
    assert ns == [2*d for d in ds]
    return sum(ns)-2


def curve_block(p,s):
    # Finite search, not required for the Hasse-Weil existence theorem.
    for v in combinations_with_replacement(range(2,(p+1)//2),s-1):
        if len(set(v)) != len(v): continue
        w = (1,)+v
        if all(sum(pow(x,2*j,p) for x in w)%p==0 for j in range(1,s-1)):
            return w
    return None


def main():
    checks=0
    for s in range(3,21):
        m=2*s
        for p in range(2*m+1, 501):
            if not isprime(p) or (p-1)%m: continue
            a=block(p,s)
            ds=moments(p,[(x,0) for x in a]+[(0,x) for x in a])
            assert min(ds)==s
            assert sum(2*d for d in ds)==m*(p+1)+(m*m if (p-1)%(2*m)==0 else 0)
            checks+=1
    print(f'Root-of-unity constructions verified: {checks}')
    for p,extras in [(13,[(0,3),(0,4),(3,0),(4,0)]),
                     (19,[(0,7),(0,8),(7,0),(8,0)]),
                     (23,[(0,3),(1,7),(3,22),(9,20)]),
                     (29,[(0,2),(0,12),(2,3),(13,4)])]:
        print(f'p={p}: independent exact cyclotomic norm tree valuation = {graph_check(p,[(1,0),(0,1)]+extras)}')
    for s,p in [(3,17),(3,23),(3,29),(4,19),(4,71),(4,101),(5,23),(5,37)]:
        if (p-1)%(2*s)==0: continue
        w=curve_block(p,s)
        if w is None:
            print(f'curve s={s}, p={p}: no witness in normalized search (small prime)'); continue
        ds=moments(p,[(x,0) for x in w]+[(0,x) for x in w])
        N=sum(pow(z,2*s-2,p)==p-1 for z in range(1,p))
        g=gcd(2*s-2,p-1)
        assert N==(g if ((p-1)//g)%2==0 else 0)
        assert sum(2*d for d in ds)==(2*s-2)*(p+1)+2*N
        print(f'curve s={s}, p={p}: block={w}, A={sum(2*d for d in ds)}')
    for s in range(3,9):
        D=2**(s-2)*factorial(s-2)
        genus=1+D*((s-2)*(s-1)-s)//2
        assert genus>=0
        nplanes=comb(2*s,s)*((2**(s-1))*factorial(s-1))**2//2
        print(f's={s}: curve degree={D}, genus={genus}, top row planes={nplanes}')

if __name__=='__main__': main()
