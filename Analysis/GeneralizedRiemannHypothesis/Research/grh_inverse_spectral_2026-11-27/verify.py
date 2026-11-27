#!/usr/bin/env python3
"""Exact finite algebra checks + illustrative high-precision interpolation.
No numerical calculation is used in the proofs of the infinite theorems.
Requires sympy and mpmath.
"""
import itertools as it
import math
import sympy as sp
import mpmath as mp


def subsets(n):
    return [J for k in range(n+1) for J in it.combinations(range(n), k)]


def minor(A, J):
    return A.extract(J,J).det() if J else sp.Integer(1)


def exact_checks():
    n=3
    a,b=sp.symbols('a b')
    X=sp.symbols('X1:4')
    L=sp.Matrix([[a,-a,0],[-a,a+b,-b],[0,-b,b]])
    expected=X[0]*X[1]*X[2]+a*X[1]*X[2]+(a+b)*X[0]*X[2]+b*X[0]*X[1]+a*b*sum(X)
    assert sp.expand((L+sp.diag(*X)).det()-expected)==0
    for A in [L, sp.Matrix([[1,2,-1],[2,3,4],[-1,4,5]])]:
        expansion=sum(minor(A,tuple(i for i in range(n) if i not in S))*sp.prod(X[i] for i in S) for S in subsets(n))
        assert sp.expand((A+sp.diag(*X)).det()-expansion)==0
    assert L.subs({a:2,b:3}).charpoly().as_expr()==L.subs({a:3,b:2}).charpoly().as_expr()
    print('Exact determinant identity and ordinary cospectral example: PASS')
    # Check induced characters span the arithmetic coefficient vectors.
    Q=math.lcm(5,8,12)
    units=[u for u in range(Q) if math.gcd(u,Q)==1]
    C=sp.Matrix([[sp.kronecker_symbol(d,u) for u in units] for d in [5,8,12]])
    assert C*C.T==len(units)*sp.eye(3)
    print(f'Character orthogonality at Q={Q}: PASS; {len(units)} columns, rank={C.rank()}')
    # Test every labelled zero-diagonal symmetric 4x4 matrix with edge values -1,0,1.
    # A switching signature is lexicographically minimal upper-triangle tuple.
    n=4; edges=list(it.combinations(range(n),2)); Jlist=subsets(n)
    def signature(vals):
        return min(tuple(vals[k]*d[i]*d[j] for k,(i,j) in enumerate(edges))
                   for d in it.product((-1,1),repeat=n))
    def profile(vals):
        A=sp.zeros(n)
        for v,(i,j) in zip(vals,edges): A[i,j]=A[j,i]=v
        return tuple(minor(A,J) for J in Jlist)
    profile_to_sig={}; sig_to_profile={}
    for vals in it.product((-1,0,1),repeat=len(edges)):
        sig=signature(vals); pr=profile(vals)
        assert profile_to_sig.setdefault(pr,sig)==sig
        assert sig_to_profile.setdefault(sig,pr)==pr
    print(f'Principal-minor vs switching fibers: PASS; {3**len(edges)} matrices, {len(profile_to_sig)} classes')


def interpolation():
    mp.mp.dps=100
    ds=[5,8,12]; n=len(ds)
    chars=[[int(sp.kronecker_symbol(d,r)) for r in range(d)] for d in ds]
    Slist=[S for S in subsets(n) if len(S)<n]
    A=sp.Matrix([[2,-2,0],[-2,5,-3],[0,-3,3]])
    exact=[minor(A,tuple(i for i in range(n) if i not in S)) for S in Slist]
    V=mp.matrix(len(Slist)); rhs=mp.matrix(len(Slist),1)
    for k in range(len(Slist)):
        s=mp.mpf(2+k)
        g=[]
        for q,chi in zip(ds,chars):
            l=mp.dirichlet(s,chi)
            ld=mp.dirichlet(s,chi,derivative=1)
            g.append(1j*(mp.log(q/mp.pi)/2+mp.digamma(s/2)/2+ld/l))
        # Independent right-hand side: determinant evaluated numerically, not minor expansion.
        B=mp.matrix([[mp.mpf(int(A[i,j]))+(g[i] if i==j else 0) for j in range(n)] for i in range(n)])
        rhs[k]=mp.det(B)-mp.fprod(g)
        for ell,S in enumerate(Slist): V[k,ell]=mp.fprod(g[i] for i in S)
    x=mp.lu_solve(V,rhs)
    err=max(abs(x[i]-int(exact[i])) for i in range(len(Slist)))
    cond=mp.cond(V)
    assert err<mp.mpf('1e-65')
    print('Numerical right-half-plane interpolation (NOT certified interval arithmetic)')
    print('  s=2,...,8; character conductors 5, 8, 12; precision=100 decimal digits')
    print('  S (one-based), recovered coefficient, exact coefficient:')
    for i,S in enumerate(Slist):
        print(f'  {tuple(j+1 for j in S)!s:10} {mp.nstr(x[i],18):45} {exact[i]}')
    print('  max absolute error:',mp.nstr(err,8))
    print('  estimated infinity-norm condition number:',mp.nstr(cond,8))
    print('Interpolation: PASS')

if __name__=='__main__':
    exact_checks()
    interpolation()
