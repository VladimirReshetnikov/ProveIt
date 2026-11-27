"""Exact rational verification of the filter-width Hessian. Requires SymPy."""
from math import factorial, comb
from functools import cache
from itertools import combinations

import sympy as s
from sympy.functions.combinatorial.numbers import stirling

p, z = s.symbols("p z")


@cache
def cumulant(r):
    if r == 1:
        return p
    return s.expand(p*(1-p)*s.diff(cumulant(r-1), p))


@cache
def mean(r):
    return s.expand((-1)**((r-1)//2)*cumulant(r)/factorial(r-1))


def beta(n_nodes, n):
    a = s.Rational(factorial(n_nodes+n-1)*factorial(n_nodes-n),
                   factorial(n_nodes-1)*factorial(n_nodes))
    return (a-1)/((2*n-1)*n*(n-1))


@cache
def legendre_coefficient(n, r):
    value = sum((-1)**(k-1)*k*factorial(k-1)*stirling(r,k,kind=2)
                * s.Rational(factorial(k-1)**2, factorial(k-n)*factorial(k+n-1))
                for k in range(n, r+1))
    return s.Rational((2*n-1)*(-1)**((r-1)//2),factorial(r-1))*value


def diagonal_gram(n_nodes, r, t):
    return sum(beta(n_nodes,n)*legendre_coefficient(n,r)*legendre_coefficient(n,t)
               for n in range(3,min(r,t)+1,2))


@cache
def node_shifts(n_nodes, r):
    # Independent construction from Taylor interpolation at z=1.
    v = s.symbols("v")
    euler = s.expand(s.series((v/s.log(1+v))**r,v,0,r).removeO().subs(v,z-1))
    base = (z-1)**n_nodes
    node_poly = s.Poly((-1)**((r-1)//2)*(z-1)**(n_nodes-r)*euler,z)
    assert node_poly.eval(0) == 0
    return [node_poly.nth(j)/s.Poly(base,z).nth(j) for j in range(n_nodes+1)]


def integrate_polynomial(poly):
    return sum(a/(j+1) for (j,),a in s.Poly(poly,p).terms())


def direct_gram(n_nodes, r, t):
    a, b = node_shifts(n_nodes,r), node_shifts(n_nodes,t)
    prob = [comb(n_nodes,j)*p**j*(1-p)**(n_nodes-j) for j in range(n_nodes+1)]
    first = s.expand(sum(q*w for q,w in zip(prob,a)))
    second = s.expand(sum(q*w for q,w in zip(prob,b)))
    assert first == mean(r) and second == mean(t)
    covariance = sum(q*x*y for q,x,y in zip(prob,a,b))-first*second
    return integrate_polynomial(s.cancel(covariance/(p*(1-p))))


if __name__ == "__main__":
    tested = 0
    minors = 0
    for n_nodes in range(3,10):
        ranks = list(range(3,n_nodes+1,2))
        for index,r in enumerate(ranks):
            decomposition = sum(legendre_coefficient(n,r)*s.legendre(n-1,2*p-1)
                                for n in ranks if n <= r)
            assert s.expand(decomposition-s.diff(mean(r),p)) == 0
            for t in ranks[index:]:
                value = diagonal_gram(n_nodes,r,t)
                assert value == direct_gram(n_nodes,r,t)
                tested += 1
        gram = s.Matrix([[diagonal_gram(n_nodes,r,t) for t in ranks] for r in ranks])
        for order in range(1,len(ranks)+1):
            subsets = list(combinations(range(len(ranks)),order))
            for rows in subsets:
                for cols in subsets:
                    assert gram.extract(rows,cols).det() > 0
                    minors += 1
        if n_nodes in (5,7):
            print(f"N={n_nodes}, odd coordinates {ranks}, pi-normalized Gram matrix")
            print(s.Matrix([[diagonal_gram(n_nodes,r,t) for t in ranks] for r in ranks]))
    print(f"Verified {tested} diagonal and mixed entries by direct covariance integration.")
    print(f"Verified strict positivity of all {minors} nonempty minors at these ranks.")
