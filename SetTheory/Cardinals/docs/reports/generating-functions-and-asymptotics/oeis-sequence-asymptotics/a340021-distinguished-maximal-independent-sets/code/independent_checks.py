"""Independent finite certificates for Report206 on A340021.
No imports from the producer's verifier. Explicit exceptions survive python -O.
Finite checks certify finite/formal identities only, not asymptotic remainders.
"""
from itertools import permutations
from math import factorial
from fractions import Fraction
import json
import sympy as S

OEIS = [1,1,2,5,16,66,407,3948]

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def induced_orbits(items, action):
    unused=set(items)
    orbits=[]
    while unused:
        first=next(iter(unused))
        orbit=[]
        x=first
        while x in unused:
            unused.remove(x)
            orbit.append(x)
            x=action(x)
        require(x == first, 'action did not close into an orbit')
        orbits.append(tuple(orbit))
    return orbits

def fixed_count(pi, tau):
    """Construct edge orbits on actual permutations; no gcd/cycle formula.
    Inclusion-exclusion on uncovered white vertices enforces maximality.
    """
    k,m=len(pi),len(tau)
    white=induced_orbits([(i,j) for i in range(m) for j in range(i+1,m)],
                         lambda e: tuple(sorted((tau[e[0]],tau[e[1]]))))
    cross=induced_orbits([(i,j) for i in range(k) for j in range(m)],
                        lambda e: (pi[e[0]],tau[e[1]]))
    touched=[sum(1<<j for j in set(e[1] for e in orbit)) for orbit in cross]
    legal=0
    for forbidden in range(1<<m):
        available=sum(not (mask & forbidden) for mask in touched)
        legal += (-1 if forbidden.bit_count()%2 else 1)*(1<<available)
    require(legal >= 0, 'negative inclusion-exclusion count')
    return (1<<len(white))*legal

def permutation_burnside(n,k):
    total=sum(fixed_count(pi,tau)
              for pi in permutations(range(k))
              for tau in permutations(range(n-k)))
    divisor=factorial(k)*factorial(n-k)
    require(total % divisor == 0, 'noninteger permutation Burnside count')
    return total//divisor

def symbolic_checks():
    z,y=S.symbols('z y')
    formal=[]
    # Direct expansion of the exact ratio for fixed k, with symbolic y.
    # The expansion is taken only after removing the removable singularity.
    for k in range(1,9):
        R=5
        log_dom=S.series((1/z-k)*S.log(1-y*z)+y,z,0,R+1).removeO()
        direct=S.series(S.prod(1-i*z for i in range(k))*S.exp(log_dom),z,0,R+1).removeO().expand()
        C=[S.Integer(0)]+[-S.Rational(1,r)*sum(i**r for i in range(k))
                          + S.Rational(k,r)*y**r-S.Rational(1,r+1)*y**(r+1)
                          for r in range(1,R+1)]
        P=[S.Integer(1)]
        for q in range(1,R+1):
            P.append(S.expand(sum(r*C[r]*P[q-r] for r in range(1,q+1))/q))
        for q in range(R+1):
            require(S.expand(direct.coeff(z,q)-P[q]) == 0,
                    f'exact ratio coefficient mismatch k={k} q={q}')
        formal.append(k)
    # General symbolic shifted-Stirling coefficients obey the exact factorial
    # shift: p(j+1,z) = p(j,z)/(1+(j+1)z).
    j=S.symbols('j')
    R=6
    C=[S.Integer(0)]+[S.Rational((-1)**r,r*(r+1))*S.bernoulli(r+1,j+1)
                      for r in range(1,R+1)]
    P=[S.Integer(1)]
    for q in range(1,R+1):
        P.append(S.expand(sum(r*C[r]*P[q-r] for r in range(1,q+1))/q))
    for q in range(R+1):
        shifted=S.expand(sum(P[q-r]*(-(j+1))**r for r in range(q+1)))
        require(S.expand(P[q].subs(j,j+1)-shifted) == 0,
                f'Stirling exact shift mismatch order={q}')
    require(S.expand(P[1]+j*(j+1)/2+S.Rational(1,12)) == 0,'wrong p1')
    expected_base=[S.Integer(1),-S.Rational(1,12),S.Rational(1,288),
                   S.Rational(139,51840),-S.Rational(571,2488320)]
    require([p.subs(j,0) for p in P[:5]] == expected_base,'wrong reciprocal Stirling base coefficients')
    # Symbolic cancellation in the displayed closed inverse. q=log x,
    # h=1/x, b=log(2*pi), M=log(mu_0(x)). Terms of orders x and 1 must vanish.
    h,a,q,b,M=S.symbols('h a q b M', nonzero=True)
    d=(q-1+a/2)/a
    c=(-a*d*d/2+(q+a/2)*d+(b+q)/2-M)/a
    t=1/h+d+c*h
    logt=q+S.series(S.log(1+d*h+c*h*h),h,0,4).removeO()
    residual=S.expand(a*t*t/2-a*t/2-(t+S.Rational(1,2))*logt+t-b/2+M-a/(2*h*h))
    for power in [-2,-1,0]:
        require(S.simplify(residual.coeff(h,power)) == 0,
                f'inverse failed at power {power}')
    # Algebraic identities behind the local switching and uniform pair bounds.
    yy,m,rr,E=S.symbols('yy m rr E', positive=True)
    # E=exp(yy/2), rr=yy*E/(m+1). Independently eliminate E.
    Aactual=m/(2*yy*E**2)
    require(S.simplify(Aactual.subs(E,rr*(m+1)/yy)-m*yy/(2*(m+1)**2*rr**2)) == 0,
            'switch lower ratio')
    B2_squared=yy**2*E/(4*(m+2)**2)
    require(S.simplify(B2_squared.subs(E,rr*(m+1)/yy)-yy*(m+1)*rr/(4*(m+2)**2)) == 0,
            'switch upper ratio')
    Bcubed=yy**3*E**3/(m+1)**3
    require(S.simplify(Bcubed.subs(E**3,m*(m+1)/(2*yy**2))-yy*m/(2*(m+1)**2)) == 0,
            'adjacent-pair minimax identity')
    return {
        'direct_formal_expansion_symbolic_y_k':formal,
        'direct_formal_expansion_order':5,
        'symbolic_stirling_shift_order':6,
        'reciprocal_stirling_base_through_order':4,
        'displayed_inverse_cancelled_powers':[-2,-1,0],
        'p_coefficients_through_order_3':[str(p) for p in P[:4]],
    }

def main():
    rows=[]
    for n in range(8):
        row=[permutation_burnside(n,k) for k in range(n+1)]
        require(sum(row)==OEIS[n],f'independent permutation total mismatch n={n}')
        rows.append(row)
    return {'status':'PASS','method':'Actual permutation edge orbits plus inclusion-exclusion, independent of the cycle-type formula',
            'permutation_burnside_rows':rows,'symbolic':symbolic_checks(),
            'scope':'Exact finite and symbolic identities only; asymptotic errors require the proof in Report206.'}

if __name__=='__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
