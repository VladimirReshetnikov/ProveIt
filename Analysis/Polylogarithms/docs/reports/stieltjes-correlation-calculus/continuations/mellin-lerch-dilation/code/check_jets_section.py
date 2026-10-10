"""Independent audit of sections/03-jets.tex; does not edit deliverables."""
import mpmath as mp
import sympy as sp
import json
from pathlib import Path

mp.mp.dps=42

def finite_formula(s,r,a):
    return (mp.zeta(s-r,1-a)-sum(mp.rf(s-r,j)*mp.zeta(s-r+j)*a**j/mp.factorial(j) for j in range(r)))/mp.rf(s-r,r)-a**r/mp.factorial(r)*mp.zeta(s)

def entire_value(s,r,a):
    if s in range(1,r+2):
        # Cauchy mean of the complete meromorphic spelling: all nodes
        # avoid its removable factors, no individual singular term is used.
        rho=mp.mpf('0.03')
        N=40
        return sum(finite_formula(s+rho*mp.e**(2j*mp.pi*k/N),r,a) for k in range(N))/N
    return finite_formula(s,r,a)

def anchored_integral(s,r,a):
    def f(t):
        if s==1:
            diff=-mp.digamma(1-a*t)-mp.euler
        else:
            diff=mp.zeta(s,1-a*t)-mp.zeta(s)
        return (1-t)**(r-1)*diff
    return a**r/mp.factorial(r-1)*mp.quad(f,[0,1])

def record(name,lhs,rhs,threshold='1e-35'):
    error=abs(lhs-rhs)
    rel=error/max(1,abs(lhs),abs(rhs))
    row={'name':name,'lhs':mp.nstr(lhs,37),'rhs':mp.nstr(rhs,37),'absolute_error':mp.nstr(error,8),'scaled_error':mp.nstr(rel,8),'passed':rel<mp.mpf(threshold)}
    print(json.dumps(row),flush=True)
    return row

def symbolic_checks():
    u=sp.symbols('u')
    gamma,g1,g2=sp.symbols('gamma gamma1 gamma2')
    laurent=1/u+gamma-g1*u+g2*u**2/2
    resonant=sp.expand(-sp.Rational(1,2)*(u-1)*u*laurent)
    r2_values=[sp.expand(resonant).coeff(u,k)*sp.factorial(k) for k in range(3)]
    assert r2_values==[sp.Rational(1,2),(gamma-1)/2,-gamma-g1]
    # Derivative at s=1 of J3(1,s;1)=1/2[(s-2)zeta(s-1)-(s-1)zeta(s)].
    lp=sp.symbols('log_2pi')
    zeta_at_zero=-sp.Rational(1,2)-lp*u/2+sp.Symbol('zeta2_at_zero')*u**2/2
    j3=sp.expand(((u-1)*zeta_at_zero-u*laurent)/2)
    derivative=sp.expand(j3).coeff(u,1)
    assert derivative==lp/4-sp.Rational(1,4)-gamma/2
    return {'resonant_s_minus_1':[str(v) for v in r2_values],'third_pole_first_derivative':str(derivative),'passed':True}

if __name__=='__main__':
    rows=[]
    cases=[(1,1,mp.mpc('.3','.1')),(1,3,mp.mpf('.25')),(2,3,mp.mpc('.25','.15')),(3,4,mp.mpc('-.3','.1')),(4,3,mp.mpc('.2','-.1')),(mp.mpc('.6','.2'),2,mp.mpc('.3','.1')),(0,3,mp.mpf('.3'))]
    for s,r,a in cases:
        rows.append(record(f'P_(s={s},r={r})(a={a}): finite expression versus anchored integral',entire_value(s,r,a),anchored_integral(s,r,a)))
    a=mp.mpf('.3')
    rows.append(record('P_1 gamma primitive',entire_value(1,1,a),mp.loggamma(1-a)-mp.euler*a))
    for m in (1,2):
        # Direct antiderivative of generalized Stieltjes differences.
        integral=(-1)**m*a*mp.quad(lambda t:mp.stieltjes(m,1-a*t)-mp.stieltjes(m),[0,1])
        jets=(mp.diff(lambda s:mp.zeta(s,1-a)-mp.zeta(s),0,m+1)/(m+1)-a*(-1)**m*mp.stieltjes(m))
        rows.append(record(f'anchored Stieltjes primitive m={m}',integral,jets))
    beta_value=-mp.diff(lambda b:mp.beta(b,3-b),1)
    rows.append(record('rational Li_-1 logarithmic integral via independent beta derivative',beta_value,mp.mpf('.5')))
    output={'working_precision':mp.mp.dps,'symbolic':symbolic_checks(),'numerical':rows,'scope':'Independent checks of the jets section; not a complete numerical check of polylogarithm order-derivative kernels.'}
    (Path(__file__).resolve().parents[1] / 'results' / 'jets_checks.json').write_text(json.dumps(output,indent=2)+'\n')
    assert all(x['passed'] for x in rows)
