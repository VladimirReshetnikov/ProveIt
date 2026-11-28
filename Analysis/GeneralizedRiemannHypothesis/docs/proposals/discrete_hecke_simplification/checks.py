#!/usr/bin/env python3
"""Exact, finite regression tests; not a formal proof. Python standard library only."""
from fractions import Fraction as F
from itertools import permutations, product, combinations
from math import factorial, prod, comb
from random import Random


def sign(p):
    return (-1)**sum(a>b for i,a in enumerate(p) for b in p[i+1:])


def det(a):
    n=len(a)
    if not n: return 1
    a=[list(map(F,r)) for r in a]
    val=F(1)
    for i in range(n):
        j=next((j for j in range(i,n) if a[j][i]),None)
        if j is None: return 0
        if j!=i: a[i],a[j]=a[j],a[i]; val=-val
        x=a[i][i]; val*=x
        for j in range(i+1,n):
            y=a[j][i]/x
            for l in range(i+1,n): a[j][l]-=y*a[i][l]
    assert val.denominator==1
    return int(val)


def cycles(p):
    seen=set(); out=[]
    for i in range(len(p)):
        if i in seen: continue
        j=i; n=0
        while j not in seen: seen.add(j); n+=1; j=p[j]
        out.append(n)
    return out


def compose(p,q): return tuple(p[q[i]] for i in range(len(p)))


def step(nu,P,eps,sigma):
    N=len(eps); k=len(sigma[0]);
    return tuple(eps[j]*(P*nu[((j+1)%N)*k+b]-nu[j*k+sigma[j][b]]) for j in range(N) for b in range(k))


def cone(nu,P,eps,k):
    N=len(eps)
    for j,e in enumerate(eps):
        for b in range(k-1):
            if e==1 and P*nu[((j+1)%N)*k+b+1]>nu[j*k+b]: return False
            if e==-1 and nu[j*k+b+1]>P*nu[((j+1)%N)*k+b]: return False
    return True


def stepmatrix(k,P,eps,sigma):
    n=k*len(eps)
    cols=[step(tuple(int(i==j) for i in range(n)),P,eps,sigma) for j in range(n)]
    return [list(r) for r in zip(*cols)]


def permtests():
    count=0
    for k,N,P in [(1,2,2),(2,2,2),(2,3,3),(3,2,2),(3,3,3),(4,2,2)]:
        ps=list(permutations(range(k))); eps=tuple((-1)**j for j in range(N))
        for ss in product(ps,repeat=N):
            tau=tuple(range(k))
            for p in ss: tau=compose(tau,p)
            q=P**N
            assert abs(det(stepmatrix(k,P,eps,ss)))==prod(q**l-1 for l in cycles(tau))
            count+=1
    print('Cycle-determinant identities:',count)
    count=0
    for k in range(1,8):
        for q in [2,3,4,9,25]:
            v=sum((F(sign(t),prod(q**l-1 for l in cycles(t))) for t in permutations(range(k))),F(0))
            assert F((q-1)**k,factorial(k))*v==F((q-1)**k,prod(q**l-1 for l in range(1,k+1)))
            count+=1
    print('Exact alternating orbit / inverse-flag identities:',count)


def pointtests():
    count=0
    for k,N,P,vals in [(2,2,2,range(-2,3)),(3,2,2,range(-1,2)),(2,3,3,range(-1,2)),(3,1,2,range(-3,4))]:
        ps=list(permutations(range(k))); ss=list(product(ps,repeat=N)); identity=(tuple(range(k)),)*N
        eps=tuple((-1)**j for j in range(N))
        signs=[prod(map(sign,s)) for s in ss]
        for nu in product(vals,repeat=k*N):
            left=0; right=0
            for s,sgn in zip(ss,signs):
                reorder=tuple(nu[j*k+s[j][b]] for j in range(N) for b in range(k))
                left+=int(min(step(reorder,P,eps,identity))>0 and cone(reorder,P,eps,k))
                right+=sgn*int(min(step(nu,P,eps,s))>0)
            assert left==right and left in (0,1)
            count+=1
    print('Pointwise signed sorting identities (including ties):',count)


def inv(A):
    n=len(A); a=[list(map(F,r))+[F(i==j) for j in range(n)] for i,r in enumerate(A)]
    for i in range(n):
        j=next(j for j in range(i,n) if a[j][i]);a[i],a[j]=a[j],a[i]
        x=a[i][i];a[i]=[v/x for v in a[i]]
        for j in range(n):
            if j!=i:
                x=a[j][i];a[j]=[v-x*w for v,w in zip(a[j],a[i])]
    return [r[n:] for r in a]


def latticechecks():
    k=N=2;P=2;eps=(1,-1);q=4
    ss=list(product(permutations(range(k)),repeat=N)); ident=ss[0]
    data=[]
    for s in ss:
        A=stepmatrix(k,P,eps,s); h=abs(det(A)); adj=[[int(h*x) for x in row] for row in inv(A)]
        data.append((h,adj,prod(map(sign,s))))
    print('Finite slab (D=(1,1)), signed lattice identity; density target 1/20:')
    for M in [6,12,18,24]:
        pos=[(a,b) for a in range(1,M+1) for b in range(1,M-a+1)]
        nonneg=[(a,b) for a in range(M+1) for b in range(M-a+1)]
        counts=[0]*len(ss);cone_lattice=0
        for x,y in product(pos,repeat=2):
            z=x+y
            for i,(h,adj,sgn) in enumerate(data):
                w=[sum(v*t for v,t in zip(row,z)) for row in adj]
                if all(v%h==0 for v in w):
                    counts[i]+=1
                    if i==0 and cone(tuple(v//h for v in w),P,eps,k): cone_lattice+=1
        assert factorial(k)**N*cone_lattice==sum(c*item[2] for c,item in zip(counts,data))
        # Count the ambient cone, not just the image lattice. Rational preimage is allowed.
        h,adj,_=data[0]; ambient=0
        for x,y in product(nonneg,repeat=2):
            z=x+y;w=[sum(v*t for v,t in zip(row,z)) for row in adj]
            ambient+=int(cone(w,P,eps,k))
        print(f'  M={M:2}: signed counts {counts}, cone-image={cone_lattice:5}, ambient/M^4={F(ambient,M**4)} ({ambient/M**4:.6f})')


def vp(x,p):
    if x==0: return float('inf')
    x=abs(x); n=0
    while x%p==0: n+=1;x//=p
    return n


def smithvals(A,p):
    """Valuations of Smith factors via determinantal divisors; tiny matrices only."""
    r=len(A);c=len(A[0]);out=[];prev=0
    for k in range(1,min(r,c)+1):
        mn=min(vp(det([[A[i][j] for j in jj] for i in ii]),p) for ii in combinations(range(r),k) for jj in combinations(range(c),k))
        if mn==float('inf'): out.extend([mn]*(min(r,c)-k+1));break
        out.append(mn-prev);prev=mn
    return out


def matmul(A,B): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]


def localchecks():
    rng=Random(20261127); count=0; sharp=0
    for p in [2,3,5]:
        for d in [1,2,3]:
            for s in range(d+1):
                for trial in range(4):
                    ae=2;ue=3;a=p**ae;u=p**ue;e=d+s
                    vals=[rng.randrange(ae+1) for _ in range(d-s)]+[float('inf')]*s
                    # Q is a split inclusion. A fills missing directions via extra columns.
                    Q=[[int(i==j) for j in range(d)] for i in range(e)]
                    A=[[0]*e for _ in range(d)];B=[[0]*d for _ in range(e)]
                    for i,v in enumerate(vals):
                        if v==float('inf'): A[i][d+i-(d-s)]=1;B[d+i-(d-s)][i]=a
                        else: A[i][i]=p**v;B[i][i]=p**(ae-v)
                    # Add arbitrary u-multiples to B and mix the middle/output matrices by row operations.
                    if trial:
                        B=[[v+u*rng.randint(-2,2) for v in row] for row in B]
                        if d>1:
                            A[0]=[x+A[1][j] for j,x in enumerate(A[0])]
                            # A <- U A, B <- B U^-1; inverse column operation.
                            for i in range(e): B[i][1]-=B[i][0]
                    AB=matmul(A,B)
                    assert all((AB[i][j]-a*(i==j))%u==0 for i in range(d) for j in range(d))
                    M=matmul(A,Q); sm=smithvals(M,p)
                    bad=sum(v>ae for v in sm)
                    assert bad==s
                    C=[qrow+brow for qrow,brow in zip(Q,B)]
                    sd=smithvals(C,p)
                    budget=sum(v<=ue for v in sd)
                    assert d+bad<=budget
                    for m in [0,1,2,3,6]:
                        assert sum(min(v,m) for v in sm)<=min(ae,m)*(d-bad)+m*bad
                        if trial==0 and all(v in (ae,float('inf')) for v in sm):
                            assert sum(min(v,m) for v in sm)==min(ae,m)*(d-bad)+m*bad;sharp+=1
                    count+=1
    # Precision counterexample if u=a: A=B=0, Q=I, C=F, s=d>0.
    print('Valuation-local Smith budget examples:',count,'; sharp truncations:',sharp)
    print('Precision failure at u=a: checked by explicit A=B=0, Q=I example in report.')

if __name__=='__main__':
    permtests();pointtests();latticechecks();localchecks();print('All exact finite regressions passed.')
