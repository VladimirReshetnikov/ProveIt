"""Independent exact certificates for the polynomial (2,2,3) tail family.

No delivered code is imported. Polynomial identities prove the finite
certificate; the all-degree argument and convergence proof are in the text.
The numerical checks use ordinary partial sums, not summation regularization.
"""
from pathlib import Path
import json, sys
import sympy as s
import mpmath as mp

V = Path(__file__).resolve().parent
n, x, t, A, B = s.symbols('n x t A B')


def split_laurent(f):
    coefficients = {}
    for term in s.Add.make_args(s.expand(f)):
        k = int(term.as_powers_dict().get(n, 0))
        coefficients[k] = coefficients.get(k, 0) + term / n**k
    return (s.expand(sum(c*n**k for k, c in coefficients.items() if k >= 0)),
            {k: s.expand(c) for k, c in coefficients.items() if k < 0 and c})


def sigma(f):
    """Polynomial with value sum_{k=1}^n f(k) at nonnegative integers."""
    return s.expand(sum(c*(s.bernoulli(k[0]+1, n+1)-s.bernoulli(k[0]+1, 1))/(k[0]+1)
                        for k, c in s.Poly(f, n).terms()))


def construct(P):
    C = sigma(P/n**3)
    D = sigma(2*P/n**2)
    eraw = s.expand(2*C/n**2-2*P/n**5+D/n**3)
    epoly, eneg = split_laurent(eraw)
    fraw = s.cancel(-P/n**4+D/n**2)
    E, F = sigma(epoly), sigma(fraw)
    G = s.expand(-P/n**7+C/n**4+D/n**5-E/n**2-F/n**3)
    lam0 = sum(c*s.bernoulli(k[0]-3) for k,c in s.Poly(P,n).terms())
    lam1 = sum(k[0]*c*s.bernoulli(k[0]-3) for k,c in s.Poly(P,n).terms())
    lam2 = F.coeff(n,1)-P.coeff(n,5)/2
    assert eneg == ({-1:lam1} if lam1 else {})
    gpoly, gneg = split_laurent(G)
    expected = {-3:lam1-lam0, -2:-lam2}
    assert gneg == {k:c for k,c in expected.items() if c}
    return (C,D,E,F,gpoly), s.Matrix([lam0,lam1,lam2])


def difference(expr):
    return s.expand(expr.subs(n,n+1).subs(
        {A:A-(n+1)**-2,B:B-(n+1)**-3},simultaneous=True)-expr)


def exact_certificate(P):
    (C,D,E,F,G), conditions = construct(P)
    assert conditions == s.zeros(3,1)
    W = s.expand(P.subs(n,x+s.Rational(1,2))-P.subs(n,x-s.Rational(1,2)))
    expr = P*A**2*B+C*A**2+D*A*B+E*A+F*B
    assert s.cancel(difference(expr)-W.subs(x,n+s.Rational(1,2))*A**2*B-G.subs(n,n+1)) == 0
    assert all(p.subs(n,0)==0 for p in [P,C,D,E,F])
    return W, expr, (C,D,E,F,G)


columns = [construct(n**d)[1] for d in range(5,28,2)]
matrix = s.Matrix.hstack(*columns)
assert matrix[:,:3].det() == s.Rational(1,12600)
dimensions=[]
for count in range(1,len(columns)+1):
    null = matrix[:,:count].nullspace()
    assert len(null)==max(0,count-3)
    dimensions.append(dict(maximum_P_degree=2*count+3,dimension=len(null)))

certificates=[]
for vector in matrix.nullspace():
    vector *= s.ilcm(*(c.q for c in vector))
    vector /= s.igcd(*(int(c) for c in vector))
    P = s.expand(sum(c*n**(5+2*i) for i,c in enumerate(vector)))
    W, expr, polys = exact_certificate(P)
    certificates.append(dict(P=str(P),W=str(W)))
    print('Exact certificate degree',s.degree(P,n),'PASS',flush=True)

P = 35*n**11+126*n**9+75*n**7+4*n**5
W, expr, (C,D,E,F,G) = exact_certificate(P)
expected_W = (394240*x**10+2639616*x**8+4281984*x**6+1893344*x**4+191316*x**2+1995)/1024
assert s.expand(W-expected_W)==0

# Centered Euler--Maclaurin coefficients determine the ordinary subtraction.
aa = sum(s.bernoulli(2*j,s.Rational(1,2))*t**(2*j+1) for j in range(7))
bb = sum(s.Rational(2*j+1,2)*s.bernoulli(2*j,s.Rational(1,2))*t**(2*j+2) for j in range(7))
product = s.Poly(s.expand(aa*aa*bb),t)
Q = s.expand(sum(c*product.nth(k[0]-h)*x**h for k,c in s.Poly(W,x).terms() for h in range(k[0]+1)))
assert Q == 385*x**6/2+3626*x**4/3+s.Rational(461503,288)*x**2+s.Rational(59471,180)
H = sigma(s.expand(G+Q.subs(x,n-s.Rational(1,2))))
expected_H = n*(175770*n**6-8505*n**5+1199985*n**4-115230*n**3+1989410*n**2-411645*n+860926)/6480
assert s.expand(H-expected_H)==0
U = expr-H
assert s.cancel(difference(U)-W.subs(x,n+s.Rational(1,2))*A**2*B+Q.subs(x,n+s.Rational(1,2)))==0

# Endpoint: uncentered asymptotic expansion, independent of the subtraction.
aa = t-t**2/2+sum(s.bernoulli(2*j)*t**(2*j+1) for j in range(1,13))
bb = t**2/2-t**3/2+sum(s.bernoulli(2*j)*s.rf(3,2*j-1)/s.factorial(2*j)*t**(2*j+2) for j in range(1,13))
products = [s.Poly(s.expand(aa*aa*bb),t),s.Poly(s.expand(aa*aa),t),s.Poly(s.expand(aa*bb),t),s.Poly(aa,t),s.Poly(bb,t)]
endpoint={}
for h in range(-7,5):
    endpoint[h] = s.expand(sum(c*prod.nth(k[0]+h) for p,prod in zip([P,C,D,E,F],products)
                              for k,c in s.Poly(p,n).terms() if k[0]+h>=0)
                           -(H.coeff(n,-h) if h<=0 else 0))
assert all(endpoint[h]==0 for h in range(-7,0))
assert endpoint[0]==-s.Rational(4037,108)

controls = dict(
    changed_weight_rejected=s.cancel(difference(U)-(W+1).subs(x,n+s.Rational(1,2))*A**2*B+Q.subs(x,n+s.Rational(1,2)))!=0,
    changed_subtraction_rejected=s.cancel(difference(U)-W.subs(x,n+s.Rational(1,2))*A**2*B+(Q+1).subs(x,n+s.Rational(1,2)))!=0,
    changed_tail_shift_rejected=s.cancel(U.subs(n,n+1).subs({A:A-(n+1)**-2,B:B+(n+1)**-3},simultaneous=True)-U-W.subs(x,n+s.Rational(1,2))*A**2*B+Q.subs(x,n+s.Rational(1,2)))!=0,
    changed_endpoint_rejected=endpoint[0]!=s.Rational(4037,108))
assert all(controls.values())

numeric=[]
for dps in [70,100]:
    mp.mp.dps=dps
    wfun,qfun,ufun=[s.lambdify(args,f,'mpmath') for args,f in [(x,W),(x,Q),((n,A,B),U)]]
    errs=[]
    for cutoff in [8,32,128]:
        partial=mp.fsum(wfun(mp.mpf(k)+mp.mpf('.5'))*mp.zeta(2,k+1)**2*mp.zeta(3,k+1)
                        -qfun(mp.mpf(k)+mp.mpf('.5')) for k in range(cutoff))
        finite=ufun(mp.mpf(cutoff),mp.zeta(2,cutoff+1),mp.zeta(3,cutoff+1))
        error=abs(partial-finite)
        assert error<mp.mpf('1e-45')
        errs.append(error)
    endpoint_checks=[]
    for cutoff in [100,1000,10000]:
        finite=ufun(mp.mpf(cutoff),mp.zeta(2,cutoff+1),mp.zeta(3,cutoff+1))
        approx=mp.fsum(mp.mpf(str(endpoint[h].p))/int(endpoint[h].q)/mp.mpf(cutoff)**h for h in range(5))
        error=abs(finite-approx)
        endpoint_checks.append(dict(cutoff=cutoff,value=str(finite),four_term_asymptotic_error=str(error)))
    assert all(mp.mpf(a['four_term_asymptotic_error'])>mp.mpf(b['four_term_asymptotic_error']) for a,b in zip(endpoint_checks,endpoint_checks[1:]))
    numeric.append(dict(decimal_precision=dps,partial_sum_cases=len(errs),maximum_absolute_error=str(max(errs)),endpoint_checks=endpoint_checks))

record=dict(passed=True,imports_delivered_code=False,python_version=sys.version,sympy_version=s.__version__,mpmath_version=mp.__version__,
            coefficient_columns=len(columns),first_minor=str(matrix[:,:3].det()),dimensions=dimensions,
            certificates=certificates,first_certificate={k:str(v) for k,v in zip(['P','C','D','E','F','G','W','Q','H'],[P,C,D,E,F,G,W,Q,H])},
            endpoint_coefficients={str(k):str(v) for k,v in endpoint.items()},corruption_controls=controls,numerical=numeric,
            scope='Exact finite rational certificates and finite coefficient-space checks, with ordinary numerical partial sums. All-degree dimension and convergence follow from the written proof; no period-independence, interval, Lean, or priority claim.')
(V/'mixed223-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('All independent mixed (2,2,3) checks PASS',flush=True)
