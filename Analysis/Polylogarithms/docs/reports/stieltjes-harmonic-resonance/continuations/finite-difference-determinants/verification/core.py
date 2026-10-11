"""Exact finite-difference determinant formulas used by the verification suites.

The analytic theorems are proved in article.tex; these routines provide finite,
replayable algebra. All arguments to exact routines should be SymPy expressions.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import combinations, permutations
import sympy as sp

@lru_cache(None)
def endpoint(r: int, k: int, a: sp.Expr, s: sp.Expr) -> sp.Expr:
    if r < 2 or not 0 <= k <= 2*r-2:
        raise ValueError('Require r>=2 and 0<=k<=2r-2')
    d=2*r-2
    return -sum((-1)**j*sp.binomial(d,j)*sum(sp.Integer(l-j)**k*(a+l)**(-s)
                for l in range(j)) for j in range(1,d+1))/sp.factorial(d)

def weight(r: int, n: int | sp.Expr, a: sp.Expr, s: sp.Expr) -> sp.Expr:
    d=2*r-2
    return sum((-1)**j*sp.binomial(d,j)*(n+a+j)**(-s)
               for j in range(d+1))/sp.factorial(d)

def endpoint_matrix(r: int, a: sp.Expr, s: sp.Expr) -> sp.Matrix:
    return sp.Matrix(r,r,lambda i,j:endpoint(r,i+j,a,s))

def uv(r: int, a: sp.Expr, s: sp.Expr) -> tuple[sp.Expr,sp.Expr]:
    mat=endpoint_matrix(r,a,s)
    return sp.factor(mat.det()),sp.factor(mat[:-1,:-1].det())

def finite_moment(r: int,k: int,N: int,a: sp.Expr,s: sp.Expr) -> sp.Expr:
    return sum(sp.Integer(n)**k*weight(r,n,a,s) for n in range(N+1))

def boundary_moment(r: int,k: int,N: int,a: sp.Expr,s: sp.Expr) -> sp.Expr:
    d=2*r-2
    upper=sum((-1)**j*sp.binomial(d,j)*sum(sp.Integer(l-j)**k*(a+l)**(-s)
                for l in range(N+1,N+j+1)) for j in range(1,d+1))/sp.factorial(d)
    h=sum((a+n)**(-s) for n in range(N+1)) if k==d else 0
    return endpoint(r,k,a,s)+h+upper

def partition_direct(r: int,N: int,a: sp.Expr,s: sp.Expr) -> sp.Expr:
    out=sp.S.Zero
    for ns in combinations(range(N+1),r):
        vand=sp.prod((ns[j]-ns[i])**2 for i in range(r) for j in range(i+1,r))
        out+=vand*sp.prod(weight(r,n,a,s) for n in ns)
    return out

def harmonic_matrices(r:int, a:sp.Expr, residues:dict[tuple[int,int],sp.Expr]) -> list[sp.Matrix]:
    """c[(j,h)] is the coefficient at (x+a+j)^(-h); zero terms allowed."""
    if not residues:
        return []
    m=max(h for _,h in residues)
    def entry(k:int,q:int):
        return sum(c*sp.binomial(k,h-q)*(-a-j)**(k-h+q)
          for (j,h),c in residues.items() if q<=h<=q+k)
    return [sp.Matrix(r,r,lambda i,j:entry(i+j,q)).applyfunc(sp.cancel) for q in range(1,m+1)]

def stencil_residues(r:int, seeds:dict[tuple[int,int],sp.Expr]) -> dict[tuple[int,int],sp.Expr]:
    """Residues of Delta^(2r-2) F/(2r-2)! from finite seed residues."""
    d=2*r-2;out={}
    for (j,h),b in seeds.items():
        for l in range(d+1):
            key=(j+l,h)
            out[key]=out.get(key,0)+b*(-1)**l*sp.binomial(d,l)/sp.factorial(d)
    return out

def rank_one_type(mats:list[sp.Matrix]) -> tuple[str,sp.Expr | None]:
    """Exact classification over a characteristic-zero coefficient field.

    Returns zero, corner, geometric (with tau), or not_rank_one.
    """
    nonzero=[m for m in mats if m!=sp.zeros(m.rows)]
    if not nonzero:
        return 'zero',None
    r=nonzero[0].rows
    candidates=[m for m in nonzero if m[0,0]!=0]
    if candidates:
        tau=sp.cancel(candidates[0][0,1]/candidates[0][0,0])
        v=sp.Matrix([tau**k for k in range(r)])
        if all((m-m[0,0]*v*v.T).applyfunc(sp.cancel)==sp.zeros(r) for m in mats):
            return 'geometric',tau
        return 'not_rank_one',None
    ee=sp.zeros(r);ee[r-1,r-1]=1
    if all(m==m[-1,-1]*ee for m in mats):
        return 'corner',None
    return 'not_rank_one',None

def complete_bell(xs:list[sp.Expr]) -> sp.Expr:
    b=[sp.S.One]
    for n in range(1,len(xs)+1):
        b.append(sum(sp.binomial(n-1,k-1)*xs[k-1]*b[n-k] for k in range(1,n+1)))
    return b[-1]
