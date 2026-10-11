#!/usr/bin/env python3
"""Independent exact and Fourier-mode checks of the contact formula.

The analytic proof is in sections/03_contacts.tex of the research article.
This program does not evaluate a delta distribution pointwise.  Its
nonzero Fourier modes see every claimed contact term directly.

The correlation side uses the full meromorphic Hurwitz Gamma coefficient
at the higher spectral pole, with its local polar numerator removed.
The canonical offpoint side uses the displayed separated kernel, the
unit-coordinate finite-part basis, and the proposed E_pq correction.
The second exact construction of B uses Gamma reflection and a cosine
ratio, not the two T_0 quotients.  Numerical comparisons are diagnostics,
not interval certificates or proofs of analytic continuation.
"""
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps=85
u,v=sp.symbols('u v')
w=u+v
zs={k:sp.Symbol('Z'+str(k)) for k in range(2,7)}


def truncate(poly, degree):
    p=sp.Poly(sp.expand(poly),u,v)
    return sp.Add(*(coef*u**i*v**j for (i,j),coef in p.terms() if i+j<=degree))


def exp_series(poly, degree):
    # Here poly has minimum total degree two.
    out=sp.Integer(1)
    power=sp.Integer(1)
    for j in range(1,degree//2+1):
        power=truncate(power*poly,degree)
        out+=power/sp.factorial(j)
    return truncate(out,degree)


# Two independent coefficient constructions of B, to total degree four.
logA=sp.Add(*(zs[k]*(u**k+(-1)**k*(w**k-v**k))/k for k in range(2,7)))
Aseries=exp_series(logA,6)
Tseries=sp.cancel((Aseries-1)/(u*w))
Bseries=sp.expand(Tseries+Tseries.xreplace({u:v,v:u}))

logR=sp.Add(*(zs[k]*(u**k+v**k-w**k)/k for k in range(2,7)))
logCosRatio=-sp.Add(*((1-sp.Rational(1,2)**(2*k))*zs[2*k]
                     *((u-v)**(2*k)-w**(2*k))/k for k in range(1,4)))
Baltseries=sp.cancel((exp_series(logR+logCosRatio,6)-1)/(u*v))
even_reduction={zs[4]:sp.Rational(2,5)*zs[2]**2, zs[6]:sp.Rational(8,35)*zs[2]**3}
assert sp.expand((Bseries-Baltseries).subs(even_reduction))==0
assert sp.expand(Bseries-Bseries.xreplace({u:v,v:u}))==0
expected_low=(2*zs[2]-zs[3]*(u+v)
              +(sp.Rational(3,2)*zs[4]+zs[2]**2/2)*(u*u+v*v)
              +(zs[4]+zs[2]**2)*u*v)
assert sp.expand(truncate(Bseries,2)-expected_low)==0


def P_expr(p,z):
    return sp.expand(sp.prod(1+z/sp.Integer(j) for j in range(1,p+1)))


def H_expr(p,z):
    if p==0:
        return sp.Integer(0)
    return sp.cancel((P_expr(p,z)-1)/z)


def E_expr(p,q):
    r=p+q
    return sp.expand((-1)**p*(P_expr(r,w)*Bseries
        +sp.cancel((H_expr(r,w)-H_expr(r,v))/u)
        +sp.cancel((H_expr(r,w)-H_expr(r,u))/v)
        -H_expr(p,u)*H_expr(r,v)-H_expr(q,v)*H_expr(r,u)
        +H_expr(p,u)*H_expr(q,v)))


pairs=[(p,q) for p in range(6) for q in range(6-p)]
for p,q in pairs:
    swap=E_expr(q,p).xreplace({u:v,v:u})
    assert sp.expand(swap-(-1)**(p+q)*E_expr(p,q))==0

E00=E_expr(0,0)
co=lambda m,n:sp.expand(E00).coeff(u,m).coeff(v,n)*(-1)**(m+n)*sp.factorial(m)*sp.factorial(n)
assert co(0,0)==2*zs[2]
assert co(1,0)==zs[3]
assert sp.expand(co(2,0).subs(zs[2]**2,sp.Rational(5,2)*zs[4])-sp.Rational(11,2)*zs[4])==0
assert sp.expand(co(1,1).subs(zs[2]**2,sp.Rational(5,2)*zs[4])-sp.Rational(7,2)*zs[4])==0
for p,q,value in [(1,0,1-2*zs[2]),(1,1,1-2*zs[2]),(2,0,2*zs[2]-sp.Rational(5,4))]:
    assert sp.expand(E_expr(p,q).subs({u:0,v:0})-value)==0

# Numerical helper functions.  Use distinct constructions on the two sides.
def branch_log(n):
    assert n!=0
    return mp.log(2*mp.pi*abs(n))+mp.j*mp.pi/2*(1 if n>0 else -1)


def P_num(p,z):
    return mp.fprod(1+z/j for j in range(1,p+1))


def H_num(p,z):
    return (P_num(p,z)-1)/z if p else mp.mpf(0)


def gamma_hurwitz_finite_part(p,z,n):
    # Direct higher-pole Hurwitz coefficient plus its complete local
    # pole numerator.  This side does not use G, H, A, B, or E.
    ln=branch_log(n)
    pochhammer=mp.rf(1+z,p)
    raw=(-1)**p*pochhammer*mp.gamma(-p-z)*mp.exp((p+z)*ln)
    numerator=pochhammer/mp.factorial(p)
    polar=numerator/z*(2*mp.pi*mp.j*n)**p
    return raw+polar


def canonical_basis(p,z,n):
    # Unit-coordinate finite parts obtained from the holomorphic G
    # coefficient and the pointwise-derivative contact polynomial.
    g=-mp.expm1(mp.loggamma(1-z)+z*branch_log(n))/z
    return (2*mp.pi*mp.j*n)**p*(g+H_num(p,z))


def gamma_A(x,y):
    return mp.gamma(1-x)*mp.gamma(1+x+y)/mp.gamma(1+y)


def gamma_B(x,y):
    w=x+y
    return (gamma_A(x,y)-1)/(x*w)+(gamma_A(y,x)-1)/(y*w)


def reflection_B(x,y):
    w=x+y
    value=mp.gamma(1-x)*mp.gamma(1-y)/mp.gamma(1-w)
    value*=mp.cos(mp.pi*(x-y)/2)/mp.cos(mp.pi*w/2)
    return (value-1)/(x*y)


def E_num(p,q,x,y):
    r=p+q;w=x+y
    return (-1)**p*(P_num(r,w)*gamma_B(x,y)
        +(H_num(r,w)-H_num(r,y))/x
        +(H_num(r,w)-H_num(r,x))/y
        -H_num(p,x)*H_num(r,y)-H_num(q,y)*H_num(r,x)
        +H_num(p,x)*H_num(q,y))


def canonical_offpoint_mode(p,q,x,y,n):
    # Derivatives in the shift of the offpoint expression, canonically
    # extended separately at a=0 and a=1.  The smooth constant -B has
    # zero nonzero modes, but is retained in the zero-mode check below.
    r=p+q;w=x+y
    left=-gamma_A(x,y)/x*canonical_basis(r,w,n)
    left+=(1/x+H_num(p,x))*canonical_basis(r,y,n)
    right=-gamma_A(y,x)/y*canonical_basis(r,w,-n)
    right+=(1/y+H_num(q,y))*canonical_basis(r,x,-n)
    return (-1)**p*(left+(-1)**r*right)


def fmt(x):
    return mp.nstr(x,24)


samples=[
    (mp.mpc('0.07','0.03'),mp.mpc('-0.04','0.06')),
    (mp.mpc('-0.09','0.02'),mp.mpc('0.05','-0.04')),
    (mp.mpc('0.025','-0.045'),mp.mpc('0.065','0.035')),
]
frequencies=[-3,1,4]
threshold=mp.mpf('1e-68')
results=[]
max_abs=mp.mpf(0);max_scaled=mp.mpf(0)
b_results=[]
for sample,(x,y) in enumerate(samples):
    b_error=abs(gamma_B(x,y)-reflection_B(x,y))
    assert b_error<threshold
    b_results.append({'sample':sample,'absolute_error':fmt(b_error)})
    # The undifferentiated correlation has mean zero; the offpoint
    # canonical mean is -B and the contact delta contributes +E_00=B.
    zero_error=abs(-gamma_B(x,y)+E_num(0,0,x,y))
    assert zero_error==0
    for p,q in pairs:
        swap_error=abs(E_num(q,p,y,x)-(-1)**(p+q)*E_num(p,q,x,y))
        assert swap_error<threshold
        for n in frequencies:
            lhs=gamma_hurwitz_finite_part(p,x,-n)*gamma_hurwitz_finite_part(q,y,n)
            canonical=canonical_offpoint_mode(p,q,x,y,n)
            contact=E_num(p,q,x,y)*(2*mp.pi*mp.j*n)**(p+q)
            rhs=canonical+contact
            err=abs(lhs-rhs)
            scaled=err/(1+abs(lhs)+abs(rhs))
            assert scaled<threshold,(sample,p,q,n,fmt(err),fmt(scaled))
            max_abs=max(max_abs,err);max_scaled=max(max_scaled,scaled)
            results.append({'sample':sample,'p':p,'q':q,'frequency':n,
                            'absolute_error':fmt(err),'scaled_error':fmt(scaled)})

# Negative control: omitting the contact changes a nonzero Fourier mode.
x,y=samples[0]
p=q=0;n=1
lhs=gamma_hurwitz_finite_part(p,x,-n)*gamma_hurwitz_finite_part(q,y,n)
without_contact=canonical_offpoint_mode(p,q,x,y,n)
missing=abs(lhs-without_contact)
assert missing>1

out={
 'purpose':'Independent exact and Fourier-mode diagnostic for sections/03_contacts.tex; not an interval certificate.',
 'versions':{'mpmath':mp.__version__,'sympy':sp.__version__},
 'precision_digits':mp.mp.dps,
 'parameter_samples':[{'u':fmt(x),'v':fmt(y)} for x,y in samples],
 'frequencies':frequencies,
 'argument_derivative_pairs':len(pairs),
 'fourier_mode_checks':len(results),
 'exact_B_comparison_total_degree':4,
 'exact_B_coefficients':{f'{i},{j}':str(coef) for (i,j),coef in sp.Poly(Bseries,u,v).terms()},
 'exact_reflection_checks':len(pairs),
 'exact_displayed_coefficient_checks':7,
 'numerical_reflection_checks':len(samples)*len(pairs),
 'zero_mode_checks':len(samples),
 'B_full_Gamma_vs_reflection':b_results,
 'maximum_absolute_mode_residual':fmt(max_abs),
 'maximum_scaled_mode_residual':fmt(max_scaled),
 'configured_scaled_threshold':str(threshold),
 'missing_contact_negative_control_error':fmt(missing),
 'all_passed':True,
 'fourier_modes':results,
}
p=(Path(__file__).resolve().parents[1]/'results'/'contacts_verification.json')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['fourier_mode_checks','exact_reflection_checks',
    'zero_mode_checks','maximum_absolute_mode_residual','maximum_scaled_mode_residual',
    'missing_contact_negative_control_error','all_passed']}))
