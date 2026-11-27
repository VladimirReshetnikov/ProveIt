"""Independent exact check of the two-summand radical-transversality count."""
from itertools import combinations, product
from math import prod
import json
from pathlib import Path


def qbin(n, k, q):
    if k < 0 or k > n:
        return 0
    return prod(q**(n-i)-1 for i in range(k)) // prod(q**(k-i)-1 for i in range(k))


def gl(k, q):
    return prod(q**k-q**i for i in range(k))


def rank(rows, q):
    a=[list(row) for row in rows]
    if not a:
        return 0
    r=0
    for j in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][j]%q),None)
        if p is None:
            continue
        a[r],a[p]=a[p],a[r]
        inv=pow(a[r][j],-1,q)
        a[r]=[(x*inv)%q for x in a[r]]
        for i in range(r+1,len(a)):
            c=a[i][j]
            a[i]=[(x-c*y)%q for x,y in zip(a[i],a[r])]
        r+=1
    return r


def subspaces(r, l, q):
    for piv in combinations(range(r),l):
        free=[(i,j) for i,p in enumerate(piv) for j in range(p+1,r) if j not in piv]
        for values in product(range(q),repeat=len(free)):
            a=[[0]*r for _ in range(l)]
            for i,p in enumerate(piv):
                a[i][p]=1
            for (i,j),x in zip(free,values):
                a[i][j]=x
            yield a


def formula(r,t0,t1,l,q):
    c=r-t0-t1
    return sum(qbin(t0,k,q)*qbin(t1,k,q)*gl(k,q)*qbin(c,l-k,q)*q**((l-k)*(t0+t1-k))
               for k in range(max(0,l-c),min(l,t0,t1)+1))


results=[]
total_spaces=total_comparisons=0
for q,maxr in [(2,6),(3,4),(5,3)]:
    for r in range(maxr+1):
        counts={(t0,t1,l):0 for t0 in range(r+1) for t1 in range(r-t0+1) for l in range(r+1)}
        for l in range(r+1):
            spaces=list(subspaces(r,l,q))
            assert len(spaces)==qbin(r,l,q)
            total_spaces+=len(spaces)
            for a in spaces:
                for t0 in range(r+1):
                    for t1 in range(r-t0+1):
                        first=rank([row[t0:] for row in a],q)==l
                        second=rank([row[:t0]+row[t0+t1:] for row in a],q)==l
                        counts[t0,t1,l]+=first and second
        for (t0,t1,l),count in counts.items():
            assert count==formula(r,t0,t1,l,q),(q,r,t0,t1,l,count,formula(r,t0,t1,l,q))
            assert (count>0)==(l<=r-max(t0,t1)),(q,r,t0,t1,l)
            total_comparisons+=1
        results.append({'q':q,'radical_dimension':r,'parameter_cases':len(counts)})

output={'passed':True,'subspaces_enumerated':total_spaces,'exact_parameter_comparisons':total_comparisons,
        'scope':'Prime fields; all radical dimensions through 6 over F2, through 4 over F3, through 3 over F5; exact formula and sharp maximum transverse dimension. Not a substitute for the proof.',
        'cases':results}
print(json.dumps(output,indent=2))
