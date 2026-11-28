#!/usr/bin/env python3
"""Exact finite regressions, not a proof of the universal statements."""
import itertools as it
import math
import random
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ


def compositions(d, s):
    if s == 0:
        if d == 0: yield ()
    elif s == 1:
        yield (d,)
    else:
        for a in range(d+1):
            for tail in compositions(d-a, s-1): yield (a,)+tail


def rank_mod(rows, p):
    pivots = {}
    for row in rows:
        r = [int(x)%p for x in row]
        for i in sorted(pivots):
            if r[i]: r = [(x-r[i]*y)%p for x,y in zip(r,pivots[i])]
        if any(r):
            i = next(i for i,x in enumerate(r) if x)
            pivots[i] = [x*pow(r[i],-1,p)%p for x in r]
    return len(pivots)


def density():
    checks = 0
    for p,k,d,blocks in [(2,1,1,[0]),(3,2,1,[0,0]),(5,2,3,[0,0]),(5,2,3,[0,1])]:
        pos=[(i,j) for i in range(k) for j in range(k) if blocks[i]==blocks[j]]
        alphas=list(compositions(d,len(pos)))
        def rows():
            for x in it.product(range(p),repeat=len(pos)):
                g=S.zeros(k)
                for (i,j),a in zip(pos,x): g[i,j]=a
                if int(g.det())%p:
                    yield [math.prod(pow(v,e,p) for v,e in zip(x,alpha))%p for alpha in alphas]
        assert rank_mod(rows(),p)==len(alphas)
        checks+=1
    return checks


def orbit_case(d, blocks):
    k=len(blocks); words=list(it.product(range(k),repeat=d)); n=len(words)
    xs=S.symbols(f'x:{k*k}'); X=S.Matrix(k,k,xs)
    T={}
    for i,wi in enumerate(words):
        for j,wj in enumerate(words):
            if any(blocks[r]!=blocks[s] for r,s in zip(wj,wi)): continue
            a=[0]*(k*k)
            for r,s in zip(wj,wi): a[r*k+s]+=1
            T.setdefault(tuple(a),S.zeros(n))[i,j]=1
    H=[j for j,w in enumerate(words) if sum(w)>d-1]
    generators=[A[:,j] for A in T.values() for j in H]
    U=S.Matrix.hstack(*generators).columnspace() if generators else []
    U=S.Matrix.hstack(*U) if U else S.zeros(n,0)
    def rest(A):
        if not U.cols: return S.zeros(0)
        # Coordinates in a rational basis of the integral orbit; we only use
        # this for trace and covariance, not to infer integral ideal membership.
        B=U.gauss_jordan_solve(A*U)[0]
        assert U*B==A*U
        return B
    scale=2**(k*k*3)
    def op(poly):
        C=S.Poly(poly,*xs)
        A=S.zeros(n)
        for a,c in C.terms():
            if a in T:
                M=math.factorial(d)//math.prod(math.factorial(e) for e in a)
                A+=S.Rational(scale,M)*c*T[a]
        return A
    def avg(poly):
        A=op(poly); return A.trace()-rest(A).trace()
    assert all(rest(A).shape==(U.cols,U.cols) for A in T.values())
    if blocks==[0,0]: g=S.Matrix([[1,2],[1,3]])
    else: g=S.diag(1,3)
    P=S.ones(1,1)
    for _ in range(d): P=S.kronecker_product(P,g)
    sub=dict(zip(xs,list(g.inv()*X*g)))
    checks=0
    for a in compositions(d,k*k):
        mon=math.prod(x**e for x,e in zip(xs,a)); A=op(mon)
        assert op(S.expand(mon.subs(sub,simultaneous=True)))==P*A*P.inv()
        assert avg(S.expand(mon.subs(sub,simultaneous=True)))==avg(mon)
        if sum((i//k)*e for i,e in enumerate(a))>d-1: assert avg(mon)==0
        ev=mon.subs(dict(zip(xs,list(S.eye(k))))) if hasattr(mon,'subs') else mon
        assert A.trace()==scale*ev
        checks+=1
    # Nontrivial safe invariant polynomial at d=2: det has row weight 1.
    if d==2 and blocks==[0,0]:
        assert avg(X.det())==scale
        # Perturb by a high monomial times p^12. Congruence follows over Z_(2).
        psi=X.det()+2**12*xs[-1]**2
        diff=S.Rational(avg(psi)-scale*psi.subs(dict(zip(xs,list(S.eye(k))))))
        assert diff==0 or (int(diff.p)%2**12==0 and int(diff.q)%2==1)
    return checks


def vp(x,p):
    x=abs(int(x))
    if not x: return math.inf
    v=0
    while x%p==0: x//=p; v+=1
    return v


def factors(M,p):
    D=smith_normal_form(M,domain=ZZ)
    return [vp(D[i,i],p) for i in range(min(M.shape))]


def unimod(n,rng):
    U=S.eye(n)
    for _ in range(5):
        i,j=rng.sample(range(n),2); U[i,:]=U[i,:]+rng.randint(-2,2)*U[j,:]
    return U


def edge_checks():
    rng=random.Random(27112026); count=0
    for p in (2,3,5):
        for n in (2,3,4):
            for h in range(n+1):
                for _ in range(3):
                    aa=rng.randrange(1,4); uu=aa+rng.randrange(1,4); a=p**aa; u=p**uu
                    M=S.diag(*([p**rng.randrange(aa+1) for _ in range(n-h)]+[rng.choice([0,p**(aa+1),p**(aa+2)]) for _ in range(h)]))
                    # For nonexceptional factors choose B_top to solve M L=a.
                    L=S.diag(*([a//int(M[i,i]) for i in range(n-h)]+[1]*h))
                    F=S.zeros(n); N=S.zeros(n)
                    for i in range(n-h,n):
                        b=p**rng.randrange(aa+1); F[i,i]=b; N[i,i]=(a-int(M[i,i]))//b
                    # Tail factors beyond u need no contribution to AB.
                    for i in range(n-h): F[i,i]=p**(uu+1)
                    Q=S.eye(n).col_join(S.zeros(n)); R=S.eye(n).row_join(S.zeros(n))
                    B=L.col_join(F); A=M.row_join(N)
                    # Add perturbation divisible by u while keeping the congruence.
                    B=B+u*p*S.Matrix(2*n,n,lambda i,j: rng.randrange(-1,2) if i<n else 0)
                    W=unimod(2*n,rng); V=unimod(n,rng)
                    Q=W*Q*V; R=V.inv()*R*W.inv(); B=W*B; A=A*W.inv()
                    assert R*Q==S.eye(n)
                    assert all(int(x)%u==0 for x in A*B-a*S.eye(n))
                    s=sum(e<=uu for e in factors(Q.row_join(B),p))
                    f=factors(A*Q,p); bad=sum(e>aa for e in f)
                    assert bad<=s-n and bad==h
                    # Direct principal-minor proof tested in the original diagonal frame:
                    if h:
                        E=(N*F)[n-h:n,n-h:n]
                        assert all(int((E-a*S.eye(h))[i,j])% (a*p)==0 for i in range(h) for j in range(h))
                        assert E.det()!=0
                    for m in (0,1,aa,aa+2):
                        trunc=sum(min(e,m) for e in f)
                        assert trunc<=(n-bad)*min(aa,m)+bad*m
                        D1=unimod(n,rng)*S.diag(*[p**rng.randrange(3) for _ in range(n)])
                        D2=S.diag(*[p**rng.randrange(3) for _ in range(n)])*unimod(n,rng)
                        assert sum(min(e,m) for e in factors(D1*A*Q*D2,p))<=vp(D1.det()*D2.det(),p)+trunc
                    count+=1
    return count


if __name__=='__main__':
    print('Finite-field evaluation span checks:',density(),flush=True)
    print('Tensor monomial covariance/trace checks:',sum(orbit_case(d,b) for b in ([0,0],[0,1]) for d in range(4)),flush=True)
    print('Threshold rank and two-sided truncation cases:',edge_checks(),flush=True)
    print('PASS: exact finite regressions; no Lean elaboration or universal proof check.')
