#!/usr/bin/env python3
"""Replay the finite-field maxima and an independent matrix-tree determinant."""
import argparse
from itertools import combinations_with_replacement

S = ((1,0), (0,1), (0,2), (1,1), (3,7))

def moments(p, steps, a, b):
    xs = tuple((a*x+b*y)**2 % p for x,y in steps)
    return tuple(sum(pow(z,j,p) for z in xs)%p for j in range(1,6))

def depths(p, steps):
    return [next(j for j,m in enumerate(moments(p,steps,a,b),1) if m)
            for a,b in [(1,t) for t in range(p)]+[(0,1)]]

def enumerate_max(p):
    # Include zero: a residue-zero step is allowed, and contributes no moments.
    reps = [(x,y) for x in range(p) for y in range(p)
            if (x,y) <= ((-x)%p,(-y)%p)]
    keys = [(x*x%p,x*y%p,y*y%p) for x,y in reps]
    inverse = {key:i for i,key in enumerate(keys)}
    assert len(inverse)==len(reps)
    # Cache projected powers. Compute higher depths only at quartic roots.
    proj = [[((x+t*y)**2 % p) for t in range(p)]+[y*y%p] for x,y in reps]
    fourth = [tuple(q*q%p for q in row) for row in proj]
    counts = [0,0]
    best = [-1,-1]
    e = inverse[(1,0,0)]
    f = inverse[(0,0,1)]
    base = [x+y for x,y in zip(fourth[e],fourth[f])]
    bound = 4*(p+1)+(24 if p%10==1 else 16)
    for i,j in combinations_with_replacement(range(len(reps)),2):
        ax,ay,az = keys[i]
        bx,by,bz = keys[j]
        k = inverse.get(((-1-ax-bx)%p,(-ay-by)%p,(-1-az-bz)%p),-1)
        if k<j:
            continue
        nonzero = int(i!=0)
        counts[0] += 1
        counts[1] += nonzero
        score = 4*(p+1)
        for t,(u,v,w,z) in enumerate(zip(base,fourth[i],fourth[j],fourth[k])):
            if (u+v+w+z)%p:
                continue
            xs = [proj[a][t] for a in (e,f,i,j,k)]
            r = next(r for r in (3,4,5) if sum(pow(x,r,p) for x in xs)%p)
            score += 2*(r-2)
        assert score<=bound
        best[0] = max(best[0],score)
        if nonzero:
            best[1] = max(best[1],score)
    assert best[1]>2*(p+1)+16
    return counts,best

def bareiss(a):
    b = 1
    for k in range(len(a)-1):
        d = a[k][k]
        assert d>0   # connected graph cofactor is positive definite
        for i in range(k+1,len(a)):
            c = a[i][k]
            for j in range(k+1,len(a)):
                a[i][j],rem = divmod(d*a[i][j]-c*a[k][j],b)
                assert rem==0
            a[i][k] = 0
        b = d
    return a[-1][-1]

def cofactor(p, steps):
    N = p*p-1
    a = [[0]*N for _ in range(N)]
    for i in range(N):
        x,y = divmod(i,p)
        for u,v in steps:
            for s in (-1,1):
                j = ((x+s*u)%p)*p+(y+s*v)%p
                a[i][i] += 1
                if j<N:
                    a[i][j] -= 1
    k = bareiss(a)
    v = 0
    while k%p==0:
        k //= p
        v += 1
    return v,k%p

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("limit", nargs="?", type=int, default=61)
    args = parser.parse_args()
    print("p,normalized_including_zero,normalized_nonzero,max_including_zero,max_nonzero")
    for p in range(11,args.limit+1,2):
        if any(p%d==0 for d in range(3,int(p**0.5)+1,2)):
            continue
        (a,b),(c,d) = enumerate_max(p)
        print(f"{p},{a},{b},{c},{d}",flush=True)
    assert depths(11,S)==[2,2,5,5,5,2,2,2,5,2,2,2]
    assert cofactor(11,S)==(70,1)

if __name__=="__main__":
    main()
