"""Exact algebra routines retained with attribution from the incoming report
Alternating Tails and Spectral Defects, 2026-10-11,
verification/verify_rank_refinement.py, repository commit
da2792fc9cc8ef19c6a314be6c65e1437fbdc66b.
Only the routines needed for the order-ten dependency replay are included.
No mathematical novelty is claimed for these inherited computations.
"""
import collections
import itertools
import sympy as s
from sympy.polys.domains import QQ
from sympy.polys.rings import ring

def falling(x, k):
    return s.prod(x-j for j in range(k))

def factorial_ratio(upper, lower, difference):
    if difference >= 0:
        return s.prod(lower+j for j in range(1, difference+1))
    return 1/s.prod(upper+j for j in range(1, -difference+1))

def build_matrices(a, b, Us):
    z = s.Symbol('z')
    F, A = s.zeros(a), s.zeros(a)
    for i in range(a):
        n = b-a+i
        for ell in range(a):
            N, R = 2*(n-ell)+1, 2*b-2*a+2+2*ell
            F[i,ell] = s.factor(s.prod((2*n-r)*(2*n+3+r)
                for r in range(2*ell))/s.factorial(2*ell+1))
            W = (z+2*ell+1)*falling(2*n+2*ell+z+1, 2*i)
            total = 0
            for h in range(1, 2*i+2, 2):
                d = s.expand(sum((-1)**(h-j)*s.binomial(h,j)
                    *W.subs(z,N-j) for j in range(h+1))/s.factorial(h))
                index = a-i+ell+(h-1)//2
                total += d*falling(N,h)*Us[index-1]
            factor = factorial_ratio(R,N,1+4*ell-2*i)/(
                (2*n+1)*(2*n+2)*s.factorial(2*ell+2))
            A[i,ell] = s.factor(2*F[i,ell]+factor*total)
    return F, A

def replay_polynomial_identity(a, b, Us, P, denominator, Fdet):
    F, A = build_matrices(a,b,Us)
    assert s.cancel(F.det(method='domain-ge')-Fdet) == 0
    R, *_ = ring([b,*Us],QQ)
    row_den = [s.lcm([s.denom(A[i,j]) for j in range(a)]) for i in range(a)]
    entries = [[R.from_expr(s.cancel(row_den[i]*A[i,j]))
                for j in range(a)] for i in range(a)]
    determinant = R.zero
    for perm in itertools.permutations(range(a)):
        inversions = sum(perm[i]>perm[j] for i in range(a) for j in range(i+1,a))
        term = R((-1)**inversions)
        for i,j in enumerate(perm):
            term *= entries[i][j]
        determinant += term
    left = determinant*R.from_expr(denominator)
    right = R.from_expr(P)*R.from_expr(s.expand(Fdet*s.prod(row_den)))
    assert left == right
    return {'signed_permutation_products':s.factorial(a).__int__(),
            'cleared_determinant_terms':len(determinant)}

def polynomial_groups(P,b,Us):
    poly = s.Poly(P,b,*Us,domain=s.ZZ)
    groups = collections.defaultdict(dict)
    for ex,c in poly.terms():
        groups[ex[1:]][ex[0]] = int(c)
    return groups

def poly_add(p,q,M):
    out = p+[0]*max(0,len(q)-len(p))
    for i,c in enumerate(q):
        out[i] = (out[i]+c)%M
    return out

def poly_mul(p,q,M):
    out = [0]*(len(p)+len(q)-1)
    for i,c in enumerate(p):
        if c:
            for j,d in enumerate(q):
                out[i+j] = (out[i+j]+c*d)%M
    return out

def poly_power(p,k,M):
    out = [1]
    for _ in range(k):
        out = poly_mul(out,p,M)
    return out

def substitute_mod(groups, substitutions, degree, M):
    powers = [[poly_power(v,k,M) for k in range(degree+1)] for v in substitutions]
    out = [0]
    for ex,coefficients in groups.items():
        term = [coefficients.get(i,0)%M for i in range(max(coefficients)+1)]
        for j,e in enumerate(ex):
            if e:
                term = poly_mul(term,powers[j][e],M)
        out = poly_add(out,term,M)
    return out

def source_determinant(a,b):
    def mu(j):
        return s.bernoulli(2*j)/s.factorial(2*j) if j>=0 else s.S.Zero
    M = s.Matrix(b,b,lambda t,k:mu(t+k-a+1)*(
        s.factorial(2*b+2*t-2*a+1)/s.factorial(2*b-2*k)
        +(s.factorial(2*t+1)/s.factorial(2*a-2*k) if k<a else 0)))
    H = s.Matrix(b,b,lambda t,k:mu(t+k-a+1))
    md, hd = M.det(method='domain-ge'), H.det(method='domain-ge')
    scale = s.prod(s.factorial(2*b+2*t-2*a+1) for t in range(b))
    scale /= s.prod(s.factorial(2*b-2*k) for k in range(b))
    return md, s.cancel(md/(hd*scale))

def valuation2(x):
    n,d = s.fraction(x)
    assert n != 0
    return (int(n)&-int(n)).bit_length()-(int(d)&-int(d)).bit_length()

def evaluate_certificate(groups,a,b,denominator,b_symbol):
    powers = [[(2*s.bernoulli(2*b-2*j))**k for k in range(a+1)]
              for j in range(1,2*a)]
    numerator = s.S.Zero
    for ex,coefficients in groups.items():
        term = sum(c*b**i for i,c in coefficients.items())
        for j,e in enumerate(ex):
            term *= powers[j][e]
        numerator += term
    return s.cancel(numerator/denominator.subs(b_symbol,b))
