from itertools import combinations, combinations_with_replacement, product
from collections import Counter
from math import factorial,gcd
from functools import reduce
import json

def vectors(n):
    types=[]
    for t in combinations_with_replacement(range(n),3):
        c=tuple(t.count(j) for j in range(n));m=6
        for z in c:m//=factorial(z)
        types.append((sum(t)%n,c,m))
    weights=Counter();zero=0
    for s,c,m in types:
        for q,b,k in types:
            if s!=q:continue
            a=tuple(c[j]-b[j] for j in range(1,n))
            if sum(j*a[j-1] for j in range(1,n))%n:raise ValueError('domain')
            y=(sum(j*a[j-1] for j in range(1,n))//n,)+a[1:]
            if not any(y):zero+=m*k
            else:
                if next(t for t in y if t)<0:y=tuple(-t for t in y)
                weights[y]+=m*k
    if zero+sum(weights.values())!=n**5:raise ValueError('total')
    return weights,zero

def det(rows):
    n=len(rows)
    if n==1:return rows[0][0]
    return sum((-1)**j*rows[0][j]*det([r[:j]+r[j+1:] for r in rows[1:]]) for j in range(n))

def primes(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:out.append(n)
    return out

def normal(rows):
    d=len(rows[0])
    return tuple((-1)**j*det([r[:j]+r[j+1:] for r in rows]) for j in range(d))

def canonical(v):
    g=reduce(gcd,v)
    if not g:return None
    v=tuple(c//g for c in v)
    if next(c for c in v if c)<0:v=tuple(-c for c in v)
    return v

def dot(u,v):return sum(a*b for a,b in zip(u,v))

def classify(n):
    w,z=vectors(n);vs=sorted(w);d=n-1
    if d==1:return {'n':n,'zero':z,'max':z}
    normals={canonical(normal(list(rows))) for rows in combinations(vs,d-1)}-{None}
    ds=set()
    for ns in normals:
        ds.update(abs(dot(ns,v)) for v in vs)
    bad=sorted({p for k in ds if k for p in primes(k)})
    rational=max((z+sum(c for v,c in w.items() if not dot(a,v)),a) for a in normals)
    out={'n':n,'vectors':len(vs),'zero':z,'normal_count':len(normals),'max_scalar':max(ds),'bad_primes':bad,'rational':rational,'modular':[]}
    for p in bad:
        best=(-1,None)
        count=0
        for k in range(d):
            for tail in product(range(p),repeat=d-k-1):
                a=(0,)*k+(1,)+tail
                val=z+sum(c for v,c in w.items() if dot(a,v)%p==0)
                best=max(best,(val,a));count+=1
        out['modular'].append({'p':p,'max':best[0],'normal':best[1],'count':count})
    out['max']=max(rational[0],*(r['max'] for r in out['modular']))
    out['weights']=[{'v':list(v),'w':w[v]} for v in vs]
    return out

if __name__=='__main__':
    print(json.dumps([classify(n) for n in range(2,6)],indent=2))
