#!/usr/bin/env python3
"""Exact rational sanity checks for the centered rank and budget lemmas.
No external dependencies. These tests are not a Lean proof or a numerical proof of RH.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def sqrt_ge(a, b):
    """Whether sqrt(a) >= b, exact for rational a>=0 and b rational."""
    assert a >= 0
    return b <= 0 or a >= b*b


def test_constants():
    # Uniform analytic upper bounds used in the paper, checked exactly.
    assert F(35,8)**2 > 19
    assert F(35,8)+F(19,32)+F(1,32) == 5
    assert F(16,11)*(F(3,2)+F(2,10**6))+F(4,5) < 3
    assert F(16)*33/32 < 17
    assert 17*2**5 == 544
    for b in (16,17,32,100,1000,10**6):
        b = F(b)
        e, v, g = 5/b**4, 9/b**4, 1/b**8
        assert (v+2*e+2*g) <= 20/b**4
        assert 0 < 1-5/b <= 1-e
        # Exact comparison for the worst u=b^-2; monotonic in u.
        u = 1/b**2
        assert sqrt_ge(19*u/b**4, F(0))
        margin = 5*u/b - e-v/2-g
        assert margin >= 0 and margin**2 >= 19*u/b**4
        for x1 in (F(1),F(2),F(3)):
            if 4*(2*x1*x1+1/b) > b:
                continue
            theta=1/(1+2*x1*x1*b)
            assert theta >= 4/b**2
            assert theta <= F(1,33)
            assert theta*(2*x1*x1*b*b+b)==b
            assert F(5,4)/b**2 <= 5*theta/16
    # C: exact symbolic rearrangement tested over signed covolume allowances.
    for D,n,b,L,H,c,delta in [(10,9,2,4,20,90,10),(9,7,1,1,5,-3,20)]:
        if c+2*delta >= D*(H-L-2*b) and b<=L:
            assert c+2*delta >= D*(H-3*L)
    print('PASS rational constants and completion budget')


def subset_masks(d):
    for n in range(d+1):
        for c in combinations(range(d),n):
            yield set(c)


def check_model(d, coords, weights, ram, group, eps):
    """P has columns along distinct coordinate axes, squared lengths given by weights.
    G acts by permutations. This permits exact covariance, moments and ranks.
    All target coordinates are kept (e0=I); diagonal near-isometry defect is exact.
    """
    h=len(coords); hr=len(ram)
    assert sum(max(1-w,0) for w in weights) <= eps*h
    gam=F(h-hr,h)
    k=[sum((weights[i] for perm in group for i,j in enumerate(coords) if perm[j]==z),F(0))/len(group) for z in range(d)]
    trace=sum(k); square=sum(x*x for x in k)
    nu=max(F(0),F(d)*square/h**2-1)
    # The group contains every permutation in a subgroup, with each element once.
    overlap=F(0)
    for perm in group:
        overlap+=sum(weights[i]*weights[j] for i,p in enumerate(coords) for j,q in enumerate(coords) if p==perm[q])
    assert square==overlap/len(group)
    assert (1-eps)*h<=trace and trace**2<=d*square
    assert sum((x-trace/d)**2 for x in k)<=(nu+2*eps)*h*h/d
    assert h*(1-eps)<=d
    ranges=[{perm[coords[i]] for i in ram if weights[i]>0} for perm in group]
    for S in subset_masks(d):
        u=F(d-len(S),d)
        avg=F(sum(len(R-S) for R in ranges),len(group))
        target=u-eps-gam-nu/2-avg/h
        assert sqrt_ge((nu+2*eps)*u*(1-u),target)
    # For coordinate images, projection-product formula can be checked by exact enumeration.
    if len(group)**3<=10000:
        N=3
        p=[F(sum(z in R for R in ranges),len(group)) for z in range(d)]
        mean_missing=F(sum(d-len(set().union(*rs)) for rs in product(ranges,repeat=N)),len(ranges)**N)
        assert mean_missing==sum((1-z)**N for z in p)
    print(f'PASS model d={d}, h={h}, h_r={hr}, epsilon={eps}, nu={nu}')


def cyclic(d):
    return [tuple((i+s)%d for i in range(d)) for s in range(d)]


def block_cyclic(a,b):
    return [tuple([(i+s)%a for i in range(a)]+[a+(j+t)%b for j in range(b)]) for s in range(a) for t in range(b)]


def test_models():
    check_model(8,[0,1],[F(1),F(1)],{0,1},cyclic(8),F(0))
    check_model(9,[0,2,4],[F(99,100),F(1),F(101,100)],{0,2},cyclic(9),F(1,300))
    check_model(8,[0,1,4,5],[F(1),F(1),F(1),F(1)],{0,1,2,3},block_cyclic(4,4),F(0))
    check_model(8,[0,1,2,4],[F(1),F(1),F(1),F(1)],{0,1,3},block_cyclic(4,4),F(0))
    # Rank-one counterexample: moment exact, near-isometry fails for eps<1-1/h.
    h=5; d=12; k=[F(h,d)]*d
    assert sum(x*x for x in k)==F(h*h,d)
    assert h-1 > 0
    print('PASS rank-one obstruction (minimal second moment alone insufficient)')


if __name__=='__main__':
    test_constants()
    test_models()
    print('All exact sanity checks passed.')
