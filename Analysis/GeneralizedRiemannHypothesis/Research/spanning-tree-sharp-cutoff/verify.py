"""Exact checks, no third-party dependencies. Run with python3 verify.py."""
from itertools import product
from math import comb
from random import Random

def vp(n, p):
    assert n
    n, i = abs(n), 0
    while n % p == 0:
        n //= p
        i += 1
    return i

def shell(p, h, d, steps):
    q, s = p**h, p**(h-1)
    e = q-s
    total = 0
    for axis in range(d):   # first unit coordinate is uniquely normalized to 1
        ranges = [range(0,q,p)]*axis + [range(q)]*(d-axis-1)
        for tail in product(*ranges):
            a = tail[:axis] + (1,) + tail[axis:]
            coeff = {0:2*len(steps)}
            for v in steps:
                z = sum(x*y for x,y in zip(a,v)) % q
                for r in (z,(-z)%q):
                    if r < e:
                        coeff[r] = coeff.get(r,0)-1
                    else:  # Phi_{p^h}(Z) = sum_{k=0}^{p-1} Z^{k*s}
                        for k in range(1,p):
                            t = r-k*s
                            coeff[t] = coeff.get(t,0)+1
            b = [0]*e
            for r, c in coeff.items():  # change from Z to T = Z-1
                if c:
                    for j in range(r+1):
                        b[j] += c*comb(r,j)
            total += min(e*vp(c,p)+j for j,c in enumerate(b) if c)
    return total

def determinant(p, h, steps):
    q = p**h
    points = list(product(range(q), repeat=2))
    index = {x:i for i,x in enumerate(points)}
    a = [[0]*(q*q-1) for _ in range(q*q-1)]
    for i,(x,y) in enumerate(points[:-1]):
        a[i][i] = 2*len(steps)
        for u,v in steps:
            for sig in [-1,1]:
                j = index[((x+sig*u)%q,(y+sig*v)%q)]
                if j < len(a):
                    a[i][j] -= 1
    prev = 1   # Bareiss; all leading minors are positive for these cofactors
    for k in range(len(a)-1):
        pivot = a[k][k]
        assert pivot > 0
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                a[i][j], r = divmod(a[i][j]*pivot-a[i][k]*a[k][j],prev)
                assert r == 0
            a[i][k] = 0
        prev = pivot
    return vp(a[-1][-1],p)

def projected_order(p, a, steps):
    # Coefficient array in T for a direction from the mod-p group algebra.
    j = [0]*p
    j[0] = 2*len(steps)
    for v in steps:
        z = sum(x*y for x,y in zip(a,v)) % p
        for r in (z,(-z)%p):
            for k in range(r+1):
                j[k] -= comb(r,k)
    return next(k for k,c in enumerate(j) if c%p)

def run():
    for p, levels in [(3,4),(5,3),(7,3),(11,2),(13,2)]:
        e = p*(p-1)
        delta = (p%4 == 3)
        flat = [(1,i) for i in range(p)]
        bent = [(1+p*i*i,i) for i in range(p)]
        for h in range(1,levels+1):
            x, y = shell(p,h,2,flat), shell(p,h,2,bent)
            assert x == (p*p-1+(h-1)*(p-1)**2)*p**(h-1)+2
            assert y == (e+p+1 if h==1 else (3*e//2+delta)*p**(h-1))
            if h==1 or (p,h)==(3,2):
                assert determinant(p,h,flat) == sum(shell(p,k,2,flat) for k in range(1,h+1))-2*h
                assert determinant(p,h,bent) == sum(shell(p,k,2,bent) for k in range(1,h+1))-2*h
        if p==3:
            print('p=3, n=2, independent cofactor valuations:',
                  determinant(3,2,flat), determinant(3,2,bent))
    rng = Random(42380)
    for p, d in [(3,2),(5,2),(5,3),(7,2)]:
        for _ in range(7):
            steps = [tuple(int(i==k) for i in range(d)) for k in range(d)]
            steps += [tuple(rng.randrange(-100,101) for _ in range(d)) for k in range(p-1-d)]
            c, rem = divmod(sum(projected_order(p,a,steps)
                                for a in product(range(p),repeat=d) if any(a)),p-1)
            assert rem==0
            assert shell(p,1,d,steps)==c
            assert shell(p,2,d,steps)==c*p**(d-1)
    assert shell(5,1,1,[(1,)]+[(2,)]*16)==4
    assert shell(5,2,1,[(1,)]+[(2,)]*16)==4
    print('28 general-cutoff tests; 14 pairs of exceptional-family shells.')
    print('Beyond-cutoff first-layer boundary also checked.')

if __name__ == '__main__':
    run()
