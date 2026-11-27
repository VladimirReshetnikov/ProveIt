#!/usr/bin/env python3
"""Exact certificate for the five-step sharpness classification."""
from collections import Counter
from itertools import permutations, product

def det(a):
    n = len(a)
    out = 0
    for pi in permutations(range(n)):
        inv = sum(pi[i] > pi[j] for i in range(n) for j in range(i+1, n))
        v = (-1)**inv
        for i,j in enumerate(pi):
            v *= a[i][j]
        out += v
    return out

def instances():
    for tail in permutations(range(1,5)):
        sigma = (0,) + tail
        for signs in product((1,-1), repeat=4):
            eps = (1,) + signs
            f = [0]*5
            for i in range(5):
                f[(i+sigma[i])%5] += eps[i]
            yield sigma,eps,f

def norm(f):
    return abs(det([[f[(i-j)%5]-f[(4-j)%5] for j in range(4)]
                    for i in range(4)]))

def bareiss_det(a):
    """Fraction-free elimination with row pivoting."""
    a = [row[:] for row in a]
    scale, sign = 1, 1
    for i in range(len(a)-1):
        j = next((k for k in range(i,len(a)) if a[k][i]),None)
        if j is None:
            return 0
        if j!=i:
            a[i],a[j] = a[j],a[i]
            sign = -sign
        d = a[i][i]
        for r in range(i+1,len(a)):
            for c in range(i+1,len(a)):
                a[r][c],rem = divmod(d*a[r][c]-a[r][i]*a[i][c],scale)
                assert rem==0
            a[r][i] = 0
        scale = d
    return sign*a[-1][-1]

def sylvester_norm(f):
    """A separate determinant in the coefficient basis before quotienting."""
    if not any(f):
        return 0
    deg = max(i for i,c in enumerate(f) if c)
    g = list(reversed(f[:deg+1]))
    return abs(bareiss_det(
        [[0]*i+[1]*5+[0]*(deg-1-i) for i in range(deg)] +
        [[0]*i+g+[0]*(3-i) for i in range(4)]))

def finite(p,z,instances):
    assert z!=1 and pow(z,5,p)==1
    roots = [pow(z,i,p) for i in range(5)]
    out = {}
    for sigma,eps,f in instances:
        if sum(c*x for c,x in zip(f,roots))%p:
            continue
        S = tuple((a,s*roots[j]%p) for a,s,j in zip(roots,eps,sigma))
        if all(x==y for x,y in S):
            continue
        inds = sorted(r for r in depths(p,S) if r>2)
        out.setdefault(tuple(inds),[]).append(S)
    return out

def depths(p,S):
    for a,b in [(1,t) for t in range(p)]+[(0,1)]:
        m = [sum(pow(a*x+b*y,2*j,p) for x,y in S)%p for j in range(1,6)]
        assert m[0]==0
        yield next(i for i,n in enumerate(m,1) if n)

def canonical(p,S):
    groups = []
    for (a,b),(c,d) in permutations(S,2):
        D = (a*d-b*c)%p
        if D==0:
            continue
        for t in (1,-1):
            inv = pow(D,-1,p)
            R = [((d*x-c*y)*inv%p,t*(a*y-b*x)*inv%p) for x,y in S]
            groups.append(tuple(sorted(min((x,y),(-x%p,-y%p)) for x,y in R)))
    return min(groups)

expected_norms = {0,1,11,16,25,31,81,101,121,131,625}
expected = {
    11:(3,{(5,5):2,(5,5,5,5):30}),
    31:(2,{(5,5):2,(3,5,5,5):10}),
    101:(36,{(5,5):2,(3,3,5,5):5}),
    131:(53,{(5,5):7})
}
witnesses={11:((1,0),(0,1),(0,2),(1,1),(3,7)),
           31:((1,1),(2,29),(4,8),(8,16),(16,27))}

def main():
    cases = list(instances())
    assert len(cases)==384
    assert all(norm(f)==sylvester_norm(f) for _,_,f in cases)
    print("Multiplication and Sylvester determinants agree in all 384 cases.")
    tally=Counter(norm(f) for _,_,f in cases)
    assert set(tally)==expected_norms
    print("Norm frequencies:",sorted(tally.items()))
    zeros={(sigma,eps) for sigma,eps,f in cases if norm(f)==0}
    assert zeros=={(tuple(k*i%5 for i in range(5)),(1,)*5) for k in (1,2,3)}
    for p,(z,target) in expected.items():
        out=finite(p,z,cases)
        assert {K:len(V) for K,V in out.items()}==target
        contribution=lambda key:sum(2*(r-2) for r in key)
        key=max(out,key=contribution)
        print(f"p={p}: {target}; maximum with two depth-five directions = {4*(p+1)+contribution(key)}")
        if p in witnesses:
            reps={canonical(p,S) for S in out[key]}
            assert reps=={canonical(p,witnesses[p])}
            print(f"  Canonical extremizer: {next(iter(reps))}")
if __name__=="__main__":
    main()

