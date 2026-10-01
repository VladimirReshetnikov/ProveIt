#!/usr/bin/env python3
"""Exact companion checks for Exact Dynamics of a Three-Dimensional Keller Map.

These checks are reproducible evidence, not a replacement for the article's
all-iterate proofs and not a Lean/Rocq certificate.  Requires Python 3.10+
and SymPy.  All algebra and polynomial-composition checks are exact.
"""
from __future__ import annotations
import argparse
import json
import platform
import time
from pathlib import Path
import sympy as sp

X, Y, Z, T = sp.symbols('x y z t')
M = sp.Matrix([[3, 3, 1], [3, 2, 1], [3, 0, 1]])
N = sp.Matrix([[2, 4, 0], [2, 3, 0], [2, 1, 0]])
B = sp.Matrix([[2, 3, 0], [2, 2, 0], [2, 0, 0]])
ONE = sp.ones(3, 1)

def baseline(x, y, z):
    u = 1 + x*y
    h = u*u*z + y*y*(1 + 3*u)
    return (u*h, y + 3*x*h, x*(5 - 3*u - x*x*z))

def shear_matrix(m: int) -> sp.Matrix:
    if m < 0:
        raise ValueError('The degree of a nonzero shear must be nonnegative.')
    return sp.Matrix([[m+3,m+5,0], [m+3,m+4,0], [m+3,m+2,0]])

def tropical(w: sp.Matrix) -> sp.Matrix:
    if len(w) != 3 or any(a <= 0 for a in w):
        raise ValueError('Use a positive three-component weight vector.')
    return N*w + max(w[0] - w[1] + w[2], 0)*ONE

def degree_sequence(n: int, m: int | None = None) -> list[list[int]]:
    if n < 0:
        raise ValueError('n must be nonnegative')
    mat = M if m is None else shear_matrix(m)
    w = ONE
    out = []
    for _ in range(n+1):
        out.append([int(a) for a in w])
        w = mat*w
    return out

def uni_orbit(prime: int, steps: int, weights=(1,1,1), h=None):
    """Exact polynomial orbits on a monomial curve over F_prime.

    This restriction can cancel leading forms in special characteristic;
    the test cases deliberately avoid that issue (wall tests use F_101).
    """
    f = tuple(sp.Poly(T**a, T, modulus=prime) for a in weights)
    one = sp.Poly(1, T, modulus=prime)
    out = [[int(p.degree()) for p in f]]
    for _ in range(steps):
        x, y, z = f
        if h is not None:
            hv = sp.Poly(0, T, modulus=prime)
            for c in reversed(h):
                hv = hv*(x*y) + c
            z = z + y*y*hv
        u = one + x*y
        v = u*u*z + y*y*(one + 3*u)
        f = (u*v, y + 3*x*v, x*(5*one - 3*u - x*x*z))
        out.append([int(p.degree()) for p in f])
    return out

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args = parser.parse_args()
    started = time.time()
    checks: list[dict] = []
    def passed(name: str, details):
        checks.append({'name': name, 'status': 'PASS', 'details': details})
        print(f'PASS  {name}', flush=True)

    F = tuple(sp.expand(p) for p in baseline(X,Y,Z))
    det = sp.factor(sp.Matrix(F).jacobian([X,Y,Z]).det())
    assert det == -2
    assert tuple(p.subs({X:-1,Y:1,Z:5}) for p in F) == (0,-2,0)
    assert tuple(p.subs({X:0,Y:-2,Z:-16}) for p in F) == (0,-2,0)
    passed('baseline determinant and collision', {'determinant':str(det)})

    tau = Y + 1/X
    a,b,c = F
    g = c*tau**3 - 2*tau**2 + b*tau - 2*a
    gp = 3*c*tau**2 - 4*tau + b
    assert sp.cancel(g) == 0 and sp.cancel(gp - 2/X) == 0
    passed('cubic inverse identities', ['g(tau)=0', "g_prime(tau)=2/x"])

    # In characteristic two: B=C*tau^2 and A=tau*(B+tau+1/x).
    for expr in [X**2*(b-c*tau**2), X**2*(a-tau*(b+tau+1/X))]:
        num = sp.cancel(expr).as_numer_denom()[0]
        assert sp.Poly(num, X,Y,Z, modulus=2).is_zero
    passed('characteristic-two inverse identities', 'generic extension is described in the proof')

    for i,p in enumerate(F):
        plus, minus = list(M.row(i)), list(N.row(i))
        terms = sp.Poly(p,X,Y,Z).terms()
        assert tuple(plus) in dict(terms) and tuple(minus) in dict(terms)
        for alpha,coeff in terms:
            assert (all(alpha[j] <= plus[j] for j in range(3))
                    or all(alpha[j] <= minus[j] for j in range(3)))
    assert M-N == ONE*sp.Matrix([[1,-1,1]])
    passed('two-vertex support certificate', {'plus':M.tolist(),'minus':N.tolist()})

    L = X*Z + 3*Y
    expected_wall = (X**2*Y**3*L, 3*X**2*Y**2*L, -X**2*L)
    w = (1,2,1)
    for p,e in zip(F,expected_wall):
        terms = sp.Poly(p,X,Y,Z).terms()
        top = max(sum(w[j]*alpha[j] for j in range(3)) for alpha,_ in terms)
        init = sum(coeff*X**alpha[0]*Y**alpha[1]*Z**alpha[2]
                   for alpha,coeff in terms
                   if sum(w[j]*alpha[j] for j in range(3)) == top)
        assert sp.expand(init-e) == 0
    assert M == B + ONE*sp.Matrix([[1,0,1]])
    assert N == B + ONE*sp.Matrix([[0,1,0]])
    passed('wall initial forms', [str(p) for p in expected_wall])

    lam = sp.symbols('lambda')
    assert sp.expand(M.charpoly(lam).as_expr()-lam*(lam**2-6*lam-1)) == 0
    assert (M*M-6*M-sp.eye(3))*ONE == sp.zeros(3,1)
    assert sp.Matrix([[2,-3,1]])*M == sp.zeros(1,3)
    a0,b0,c0=sp.symbols('a b c', positive=True)
    assert sp.expand((sp.Matrix([[1,-1,1]])*M*sp.Matrix([a0,b0,c0]))[0]) == 3*a0+b0+c0
    assert sp.expand((sp.Matrix([[1,-1,1]])*N*sp.Matrix([a0,b0,c0]))[0]) == 2*a0+2*b0
    passed('matrix and invariant-cone identities', str(M.charpoly(lam).as_expr()))

    rows=degree_sequence(12)
    assert [r[0] for r in rows[:7]] == [1,7,43,265,1633,10063,62011]
    for i in range(11):
        assert rows[i+2] == [6*rows[i+1][j]+rows[i][j] for j in range(3)]
    passed('ordinary degree recurrence',rows)

    weighted=[]
    for w in [(1,1,1),(1,3,1),(1,2,1),(3,1,2),(1,1,4)]:
        actual=uni_orbit(101,3,w)
        expected=[list(w)]
        v=tropical(sp.Matrix(w))
        for n in range(1,4):
            expected.append([int(a) for a in v]);v=M*v
        assert actual == expected, (w,actual,expected)
        weighted.append({'weight':w,'degrees':actual})
    passed('weighted exact compositions over F_101',weighted)

    m=sp.symbols('m',integer=True,nonnegative=True)
    S=sp.Matrix([[m+3,m+5,0],[m+3,m+4,0],[m+3,m+2,0]])
    assert sp.expand(S.charpoly(lam).as_expr()-lam*(lam**2-(2*m+7)*lam-(m+3))) == 0
    assert sp.simplify((S*S-(2*m+7)*S-(m+3)*sp.eye(3))*ONE) == sp.zeros(3,1)
    gap=sp.expand((sp.Matrix([[m,m+2,-1]])*S*sp.Matrix([a0,b0,c0]))[0])
    assert sp.expand(gap-((2*m+1)*(m+3)*a0+(2*m*m+10*m+6)*b0)) == 0
    passed('symbolic all-shear matrix certificate',{'characteristic_polynomial':str(S.charpoly(lam).as_expr()),'gap':str(gap)})

    shears=[]
    for hs in [[1],[2,-1],[1,2,3],[4,0,1,0,-2]]:
        degree=len(hs)-1
        actual=uni_orbit(101,3 if degree<2 else 2,h=hs)
        expected=degree_sequence(len(actual)-1,degree)
        assert actual==expected
        shears.append({'coefficients_low_to_high':hs,'degrees':actual})
    passed('shear-family exact compositions over F_101',shears)

    hv = sp.symbols('hv')
    generic_shear = baseline(X, Y, Z + Y**2*hv)
    for identity in [generic_shear[1] - Y,
                     generic_shear[2] + X + X**3*Z + X**3*Y**2*hv,
                     generic_shear[0] + Y**3*generic_shear[2] - Z - Y**2*(1+hv)]:
        assert sp.Poly(identity, X,Y,Z,hv, modulus=3).is_zero
    char3=[]
    for hs in [None,[1],[2],[1,1],[2,1,1],[1,0,0,2]]:
        actual=uni_orbit(3,4,h=hs)
        if hs is None:
            lead=[1]+[7*4**(n-1) for n in range(1,5)]
        elif len(hs)==1:
            lead=[1]+[8*4**(n-1) for n in range(1,5)]
        else:
            mm=len(hs)-1;lead=[1,2*mm+8]
            for n in range(1,4):lead.append((mm+3)*lead[-1]+mm+5)
        expected=[[1,1,1]]+[[lead[n],1,lead[n]-3] for n in range(1,5)]
        assert actual==expected,(hs,actual,expected)
        char3.append({'shear':hs,'degrees':actual})
    passed('characteristic-three phase diagram',char3)

    for prime in [2,5,7,11]:
        assert uni_orbit(prime,3)==degree_sequence(3)
    passed('other small characteristics',{'primes':[2,5,7,11],'iterations':3})

    # Exact spectra certify the transverse contraction assumptions in the text.
    s10=sp.sqrt(10); v=sp.Matrix([(2+s10)/3,(7+2*s10)/9,1])
    assert sp.simplify(M*v-(3+s10)*v)==sp.zeros(3,1)
    assert (sp.eye(3)-M).det()!=0
    for mm in range(20):
        SS=shear_matrix(mm)
        assert (sp.eye(3)-SS).det()!=0
        # rho_minus=-(m+3)/rho_plus has modulus <1 since rho_plus>m+3.
        assert (mm+3)**2-(2*mm+7)*(mm+3)-(mm+3) < 0
    beta, sigma = sp.symbols('beta sigma')
    L_base = sp.Matrix([0, sigma/2, -3*sigma/2])
    assert sp.simplify((sp.eye(3)-M)*L_base-sp.Matrix([0,sigma,0])) == sp.zeros(3,1)
    L_shear = sp.Matrix([-2*beta-(m+5)*sigma,
                         (m+2)*sigma-beta,
                         beta-(4*m+11)*sigma])/(3*(m+3))
    assert sp.simplify((sp.eye(3)-S)*L_shear-sp.Matrix([beta,beta+sigma,beta])) == sp.zeros(3,1)
    passed('escape-theorem spectral hypotheses',{'baseline_eigenvector':list(map(str,v)), 'shears_checked':list(range(20))})

    result={'title':'Exact Dynamics of a Three-Dimensional Keller Map',
            'status':'All checks passed; mathematical proofs are in article.tex.',
            'python':platform.python_version(),'sympy':sp.__version__,
            'repository_pin':'a866ff9a2cdb9c5f436bb1d82ea5dca59dfee38d',
            'checks':checks,'number_of_groups':len(checks),
            'elapsed_seconds':round(time.time()-started,3)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,default=lambda x: int(x) if isinstance(x, sp.Integer) else str(x))+'\n')
    print(f'{len(checks)} groups passed. Results: {args.output}',flush=True)

if __name__=='__main__':
    main()
