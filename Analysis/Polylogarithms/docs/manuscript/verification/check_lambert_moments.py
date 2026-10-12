"""Independent symbolic and numerical checks of the Lambert moment identities.

Finite checks support the written all-order proofs; quadrature is not interval
certification. No delivered verification code is imported.
"""
from pathlib import Path
import json, sys
import sympy as S
import mpmath as mp
if sys.flags.optimize:
    raise RuntimeError('Assertions must remain enabled.')
V=Path(__file__).resolve().parent
Y,h,a=S.symbols('Y h a')
NMAX=8
P=[S.Integer(1)]
for j in range(1,NMAX+1):
    P.append(S.expand(-S.Rational(1,2*j)*S.series(
        (1+h)**S.Rational(-3,2)*(Y+S.log(1+h))**j,h,0,j
    ).removeO().coeff(h,j-1)))
# Keep psi(-1/2) as an indeterminate; evaluate higher polygammas exactly.
psi=[a]+[(-1)**(m+1)*S.factorial(m)*(2**(m+1)-1)*S.zeta(m+1)
         +2**(m+1)*S.factorial(m) for m in range(1,NMAX)]
def exp_series(log_coefficients,n):
    out=[S.Integer(1)]
    for k in range(1,n+1):
        out.append(S.expand(sum(j*log_coefficients[j]*out[k-j]
                               for j in range(1,k+1))/k))
    return out
# G(b)=1/Gamma(-b); M_k=(-1)^k G^(k)(1/2)/(k! G(1/2)).
g=exp_series([0]+[(-1)**(k+1)*psi[k-1]/S.factorial(k)
                 for k in range(1,NMAX+1)],NMAX)
M=[(-1)**k*g[k] for k in range(NMAX+1)]
Q=[];compact=[];mutants={}
for n in range(NMAX+1):
    old=0
    for j in range(n+1):
        f=P[j]
        for ell in range(n-j):
            f=S.diff(f,Y)-(j+S.Rational(1,2)+ell)*f
        old+=M[n-j]*f
    old=S.expand(old);Q.append(old)
    zpsi=[S.expand(psi[m]+sum((-1)**m*S.factorial(m)/
             (-S.Rational(1,2)+j)**(m+1) for j in range(n+1)))
          for m in range(n)]
    gg=exp_series([0]+[(zpsi[k-1]-(Y if k==1 else 0))/S.factorial(k)
                      for k in range(1,n+1)],n)
    new=S.expand(S.rf(S.Rational(1,2),n)*sum(
        (-1)**k*S.pi**(2*k)/S.factorial(2*k)*gg[n-2*k]
        for k in range(n//2+1)))
    assert S.expand(old-new)==0,n
    compact.append(new)
    if n==1:
        mutants['gamma_transfer_sign_required']=S.expand(
            old-(P[1]+M[1]/2))!=0
    if n==2:
        mutants['cosine_factor_required']=S.expand(
            old-S.rf(S.Rational(1,2),n)*gg[n])!=0
    assert S.Poly(new,Y).degree()==n
    assert new.coeff(Y,n)==(-1)**n*S.binomial(2*n,n)/4**n
    print('Gamma moment polynomial',n,'PASS',flush=True)
for n in range(NMAX):
    assert S.expand(S.diff(Q[n+1],Y)-S.diff(Q[n],Y)
                    +(n+S.Rational(1,2))*Q[n])==0
H=S.symbols('H')
q3=S.expand(Q[3].subs(Y,H+a))
assert S.expand(q3-(-5*H**3/S.Integer(16)+H**2+
    (S.Rational(13,4)+15*S.pi**2/32)*H+
    1-S.pi**2/2-S.Rational(35,8)*S.zeta(3)))==0

# Compute the Lambert chart by implicit coefficient recursion, without its
# finite Lagrange formula. A=2 is a rational diagnostic, not zeta(2).
w=S.symbols('w');A=S.Integer(2);order=5
field=S.QQ.frac_field(w)
u=[field.one]
def mul(left,right,n):
    return [sum((left[j]*right[k-j] for j in range(k+1)),
                field.zero) for k in range(n+1)]
def power(base,k,n):
    result=[field.one]+[field.zero]*n
    for _ in range(k):result=mul(result,base,n)
    return result
for n in range(1,order+1):
    U=u+[field.zero];hh=[field.zero]+U[1:]
    f=field.zero
    for k in range(2,n+1):
        logcoef=sum(S.binomial(2,j)*S.Rational((-1)**(k-j+1),k-j)
                    for j in range(min(2,k-1)+1))
        fk=field.from_sympy(S.binomial(2,k)-w*logcoef)
        f+=fk*power(hh,k,n)[n]
    f-=field.from_sympy(w/A)*U[n-1]
    if n==2:f+=field.from_sympy(w/(4*A**2))
    for j in range(n):
        cj=(-1)**(j+3)*S.zeta(-j)/S.factorial(j+3)
        f+=field.from_sympy(2*cj*w**(j+2))*power(U,j+3,n)[n-j-1]
    un=-f/field.from_sympy(2-w);u.append(un)
    un=field.to_sympy(un)
    top=S.limit((2-w)**(2*n-1)*un,w,2)
    expected=S.catalan(n-1)*2**(n-1)*(2/A-S.Rational(2,3))**n
    assert S.simplify(top-expected)==0
    assert S.simplify(un.subs(w,0))==0
    print('Lambert chart pole',n,'PASS',flush=True)

def rho(nu,t):
    return nu*mp.exp((t+nu-1)*mp.log(t)-mp.loggamma(t+nu+1))
def laplace(nu,H):
    # t=y^2 removes the smallest endpoint singularity, nu=1/2.
    def f(y):
        if not y:return 2/mp.sqrt(mp.pi) if nu==mp.mpf('.5') else 0
        return 2*y*rho(nu,y*y)*mp.exp(-H*y*y)
    return mp.quad(f,[0,1,3,10,mp.inf])
def convolution(mu,nu,t):
    def f(theta):
        x=t*mp.sin(theta)**2;y=t*mp.cos(theta)**2
        if not x or not y:return mp.mpf(0)
        return rho(mu,x)*rho(nu,y)*2*t*mp.sin(theta)*mp.cos(theta)
    return mp.quad(f,[0,mp.pi/4,mp.pi/2])
numeric=[]
for dps in [60,90]:
    mp.mp.dps=dps;lap=[];conv=[]
    for nu in map(mp.mpf,['.5','1','1.5','2']):
        for hh in map(mp.mpf,['1.1','2','7']):
            T=-mp.lambertw(-mp.exp(-hh),-1)
            error=abs(laplace(nu,hh)/T**(-nu)-1)
            assert error<mp.mpf('1e-45')
            lap.append(error)
    for mu,nu in [('.5','.5'),('.5','1.5'),('1','2')]:
        for tt in map(mp.mpf,['.2','1','4']):
            mu1,nu1=mp.mpf(mu),mp.mpf(nu)
            error=abs(convolution(mu1,nu1,tt)/rho(mu1+nu1,tt)-1)
            assert error<mp.mpf('1e-45')
            conv.append(error)
    numeric.append(dict(decimal_precision=dps,laplace_cases=len(lap),
        convolution_cases=len(conv),maximum_laplace_relative_error=str(max(lap)),
        maximum_convolution_relative_error=str(max(conv))))
    print('Quadrature at',dps,'digits PASS',flush=True)
controls=dict(
    **mutants,
    pole_sign_required=S.limit((2-w)**3*field.to_sympy(u[2]),w,2)!=-S.Rational(2,9),
    secondary_branch_required=abs(laplace(mp.mpf('.5'),2)-
        (-mp.lambertw(-mp.exp(-2),0))**(-mp.mpf('.5'))) > 1)
assert all(controls.values())
record=dict(passed=True,imports_delivered_code=False,
    python_version=sys.version, sympy_version=S.__version__,
    mpmath_version=mp.__version__,
    symbolic_polynomials=NMAX+1,derivative_recurrences=NMAX,
    exact_pole_orders=order,pole_diagnostic_A=str(A),quadrature=numeric,
    centered_Q3=str(q3),corruption_controls=controls,
    scope='Finite symbolic identities and high-precision quadrature; not interval certification or the all-order analytic proof.')
(V/'lambert-moment-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('All independent Lambert moment checks PASS',flush=True)
