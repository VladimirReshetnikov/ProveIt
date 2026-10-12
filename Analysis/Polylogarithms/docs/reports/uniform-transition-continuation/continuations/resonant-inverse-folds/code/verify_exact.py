#!/usr/bin/env python3
"""Finite exact algebra checks for Resonant Polylogarithm Inversion.

These checks support, but do not replace, the analytic proofs in article.tex.
No network access is used. Run from this directory or the package root.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]
checks: list[dict[str, object]] = []
def check(name: str, expression: s.Expr) -> None:
    ok = s.expand(expression) == 0
    if not ok:
        ok = s.simplify(expression) == 0
    checks.append({'name': name, 'passed': bool(ok)})
    if not ok:
        raise AssertionError(f'{name}: {expression}')

L, h, e, z = s.symbols('L h epsilon z')
gamma = s.Symbol('gamma')
zet = {j: s.Symbol(f'zeta{j}') for j in range(2, 8)}
st = {0: gamma, **{j: s.Symbol(f'gamma{j}') for j in range(1, 7)}}
G: dict[int, list[s.Expr]] = {}
P: dict[tuple[int, int], s.Expr] = {}
for n in range(5):
    ell = [s.Integer(0), gamma-s.harmonic(n)]
    ell += [(zet[j]+(-1)**j*s.harmonic(n,j))/j for j in range(2,7)]
    coeff = [s.Integer(1)]
    for m in range(1,7):
        coeff.append(s.expand(sum(j*ell[j]*coeff[m-j] for j in range(1,m+1))/m))
    G[n] = coeff
    for r in range(5):
        p = s.expand((-1)**r*st[r]-s.factorial(r)*sum(coeff[r+1-j]*(-L)**j/s.factorial(j) for j in range(r+2)))
        P[n,r] = p
        check(f'jet leading coefficient n={n} r={r}', p.coeff(L,r+1)-s.Rational((-1)**r,r+1))
        q = p
        for j in range(r+1):
            q=s.expand(q.subs(L,L+h)-q)
        check(f'sharp log monodromy n={n} r={r}', q-(-1)**r*s.factorial(r)*h**(r+1))
        check(f'nilpotent log monodromy n={n} r={r}', q.subs(L,L+h)-q)
        if n:
            check(f'differential jet ladder n={n} r={r}',n*p-s.diff(p,L)-n*P[n-1,r])
    if n:
        for m in range(1,7):
            check(f'Gamma recurrence n={n} degree={m}',coeff[m]+coeff[m-1]/n-G[n-1][m])

# First-order root moments: this independently produces C and D.
d, ep, kap, eta, a, K = s.symbols('delta epsilon kappa eta a K')
u=1+d
F0=s.series(u*(1-s.log(u))-1,d,0,8).removeO()
qinv=s.series(1/(-2*F0/d**2),d,0,4).removeO()
B1=-(1+d)*(K+a*s.log(1+d)+s.log(1+d)**2/2)
Delta=s.series(ep*B1+kap*u+eta*u*u/4,d,0,4).removeO()
S=[]
for j in [1,2]:
    residue=s.expand((-2)*u**(j-1)*Delta*qinv).coeff(d,1)
    S.append(s.expand(2-j*residue))
C=s.expand(S[0]/2)
# Discard degree >=2 for this first-jet comparison.
D=s.expand(S[1]/2-S[0]**2/4)
D1=s.expand(D.subs({ep:z*ep,kap:z*kap,eta:z*eta})).coeff(z,1)
check('root center epsilon coefficient',C.coeff(ep)-(-a-4*K/3))
check('root center kappa coefficient',C.coeff(kap)-s.Rational(4,3))
check('root center eta coefficient',C.coeff(eta)-s.Rational(7,12))
check('root discriminant first jet',D1-(2*kap-2*K*ep+eta/2))

# Puiseux coefficients through epsilon^(3/2), using a formal square root c.
c,J0,M = s.symbols('c J0 M')
b=-a-4*K/3
Mexpr=a*a/2+(3*a+1)*K+s.Rational(13,9)*K*K+J0
delta=c*h+b*h*h+Mexpr/c*h**3
Ftr=-delta**2/2+delta**3/6-delta**4/12-h*h*(K+(K+a)*delta+(a+1)*delta**2/2)+h**4*J0
for j in [2,3,4]:
    numerator=s.together(s.expand(Ftr).coeff(h,j)).as_numer_denom()[0]
    rem=s.rem(numerator,s.Poly(c*c+2*K,c),c)
    check(f'Puiseux equation through h^{j}',rem.as_expr())

# Exact core critical formulas verified without numerical Gamma or zeta.
N, E, U, Zeta, A0 = s.symbols('n epsilon U Zeta A0', nonzero=True)
# At criticality U^n = (n+epsilon)/(epsilon*zeta), and g exp(-e*k) U^e = n/U^n.
check('general core critical value', ((N+E)/(E*Zeta))*Zeta-E**-1*N-1)
# Derivatives at the critical point and the full-tail first variation.
Hkk=N
Huu=-N*(N+E)/U**2
Huk=N*(N+E)/U
k1=-A0*U**(N+1)/N
u1=(1-E)*A0*U**(N+2)/(N*(N+E))
check('critical value first tail variation',Hkk*k1+A0*U**(N+1))
check('critical derivative first tail variation',Huu*u1+Huk*k1+(N+1)*A0*U**N)

# Explicit logarithmic expansion of the n=1 core fold.
logg=(gamma-1)*e+(zet[2]+1)*e**2/2+(zet[3]-1)*e**3/3
zreg=1+gamma*e-st[1]*e**2+st[2]*e**3/2
logu=s.series(s.log(1+e)-s.log(zreg),e,0,4).removeO()
kcrit=s.expand((logg+(1+e)*logu)/e)
Kactual=st[1]+((gamma-1)**2+zet[2]+1)/2
Jactual=-s.Rational(1,2)+zet[3]/3+(1-gamma)*st[1]+gamma**2/2-gamma**3/3-st[2]/2
check('Gamma-zeta fold coefficient K',kcrit.coeff(e,1)-Kactual)
check('Gamma-zeta fold coefficient J',kcrit.coeff(e,2)-Jactual)

# All-sector binomial law, checked to order 18 after scaling A=1.
r=s.Symbol('r')
bs=[s.binomial(s.Rational(1,2),j)/2**j for j in range(19)]
for m in range(19):
    coeff=sum(bs[j]*bs[m-j] for j in range(m+1))
    check(f'leading exponential-sector convolution degree={m}',coeff-(1 if m==0 else s.Rational(1,2) if m==1 else 0))

ROOT.joinpath('results').mkdir(exist_ok=True)
report={'sympy_version':s.__version__,'assertions':len(checks),'all_passed':all(c['passed'] for c in checks),'scope':'Finite exact coefficient algebra only; analytic theorems are proved in article.tex.','checks':checks}
ROOT.joinpath('results/exact_checks.json').write_text(json.dumps(report,indent=2)+'\n')
coeffs={'jets':{f'n={n},r={r}':str(p) for (n,r),p in P.items()},'center_first_jet':str(C),'discriminant_first_jet':str(D1),'K':str(Kactual),'critical_kappa_second_coefficient':str(Jactual),'puiseux_third_numerator':str(Mexpr)}
ROOT.joinpath('results/symbolic_coefficients.json').write_text(json.dumps(coeffs,indent=2)+'\n')
print(f'{len(checks)} exact assertions passed.')
