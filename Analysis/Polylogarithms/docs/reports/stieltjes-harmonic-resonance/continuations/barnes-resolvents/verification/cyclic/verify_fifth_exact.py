"""Exact finite algebra supporting the convergent fifth-jet identities.
Analytic normal convergence is proved in the article, not by this script.
"""
from pathlib import Path
import json
import sympy as s
import derive_fifth_correction as dc

def main():
    A,B,C=dc.A,dc.B,dc.C
    g,q,q4=dc.g,dc.h2,dc.h4
    z,y=dc.z,dc.y
    checks=[]
    def check(name,expr):
     residual=s.factor(s.expand(expr))
     assert residual==0,(name,residual)
     checks.append({'name':name,'residual':'0'})
    # Independently entered finite correction, compared with extracted E coefficients.
    group=-(10*g**4+20*g**3+12*g*g*q+30*g*g+12*g*q+30*g+2*q*q+6*q+15)/16
    group+=(-g**4-2*g*g*q+q*q+2*q4)*y[1]/4-g*(g*g+q)*y[2]/2
    group-=(g**3+3*g*g+6*g+6+(g+1)*q)*z[1]
    group-=(3*g*g+6*g+6+q)*z[2]/2
    group+=(g*g-q)*z[1]*z[2]/2+g*z[2]**2/4
    check('Finite normalized correction',dc.xi-group)
    # Cross-check the same E construction at the preceding report's AAB derivative.
    oldE=-(g**3+g*q)/2-(3*g*g+q)/4-3*g/4-s.Rational(3,8)
    oldE-=(g*g+q+2*g+2)*z[1]+(g+1)*z[2]
    oldE+=g*z[1]*z[2]-(g**3+3*g*q+2*dc.h3)*y[1]/3-(g*g+q)*y[2]/2
    extracted_old=s.expand(2*dc.E[(2,1,0)]).subs({z[0]:-s.Rational(1,2),y[0]:-s.Rational(1,12)})
    check('Previous AAB elementary normalization',extracted_old-oldE)
    # Exact local subtractions. h is formal and accounts for every logarithmic term.
    x,h=s.symbols('x h')
    f1=h/x+z[1]-y[1]*x+s.Symbol('a2')*x*x
    f2=(h*h+q)/x+z[2]-y[2]*x+s.Symbol('b2')*x*x
    P21=h*(h*h+q)/x**2+(z[1]*(h*h+q)+z[2]*h)/x-y[1]*(h*h+q)-y[2]*h+z[1]*z[2]
    P22=(h*h+q)**2/x**2+2*z[2]*(h*h+q)/x-2*y[2]*(h*h+q)+z[2]**2
    K=f2*f2/4+h*f2*f1
    P=P22/4+h*P21
    for power in [-2,-1,0]:check('Local coefficient x^'+str(power),s.expand(K-P).coeff(x,power))
    # General fifth coefficient from the symmetric generating germ.
    L,alpha,chi=s.symbols('L alpha chi')
    e1=A+B+C;e2=A*B+B*C+C*A;e3=A*B*C
    D=e1*e1-3*e2;p2=e1*e1-2*e2
    J2=alpha*(A*A+B*B+C*C)+chi*e2
    M41=sum(u**4*v for u,v in [(A,B),(B,A),(B,C),(C,B),(C,A),(A,C)])
    M32=sum(u**3*v**2 for u,v in [(A,B),(B,A),(B,C),(C,B),(C,A),(A,C)])
    F=-5*L*z[4]*M41+20*z[2]*z[3]*M32-sum(v**5 for v in [A+B,B+C,C+A])*z[5]+120*e3*J2
    omega=s.expand(F.subs({A:1,B:1,C:1})/3)
    rhs=e3*p2*omega-120*e3*D*chi-5*(e1*e2-3*e3)*D*L*z[4]
    rhs+=20*(e1*e2**2-4*e1**2*e3+3*e2*e3)*z[2]*z[3]
    rhs+=(-2*e1**5+5*e1**3*e2-5*e1*e2**2+47*e1**2*e3-69*e2*e3)*z[5]
    check('General symbolic cyclic fifth formula',F-rhs)
    example=F.subs({A:1,B:2,C:3})-84*omega+2160*chi+720*L*z[4]-1200*z[2]*z[3]+1704*z[5]
    check('Explicit asymmetric fifth identity',example)
    check('Diagonal J2 coefficient relation',alpha+chi-(omega+10*L*z[4]-40*z[2]*z[3]+32*z[5])/120)
    # The mixed R-derivative coefficient required to extract chi.
    u,v,w=s.symbols('u v w')
    R=v*(A**3*B+A*B**3)/6+w*A*A*B*B/4+u*(A*A*B*C+A*B*B*C)/2
    cyclic=C*R+A*R.xreplace({A:B,B:C,C:A})+B*R.xreplace({A:C,B:A,C:B})
    check('Coefficient [A2 B2 C] equals R_AABB/4 + R_AABC',s.Poly(s.expand(cyclic),A,B,C).coeff_monomial(A*A*B*B*C)-(w/4+u))
    # Rectangular differences produce the local product kernel exactly.
    ua,ub,pa,pb,qa,qb=s.symbols('ua ub pa pb qa qb')
    # u is Gamma(1-A)*x^A, p is zeta(A), q is zeta(A-1).
    S=lambda ua,ub,pa,pb,qa,qb:ua*ub/x**2+(ua*pb+ub*pa)/x-ua*qb-ub*qa+pa*pb
    rect=S(ua,ub,pa,pb,qa,qb)-S(ua,1,pa,-s.Rational(1,2),qa,-s.Rational(1,12))-S(1,ub,-s.Rational(1,2),pb,-s.Rational(1,12),qb)+S(1,1,-s.Rational(1,2),-s.Rational(1,2),-s.Rational(1,12),-s.Rational(1,12))
    target=(ua-1)*(ub-1)/x**2+((ua-1)*(pb+s.Rational(1,2))+(ub-1)*(pa+s.Rational(1,2)))/x
    target-=(ua-1)*(qb+s.Rational(1,12))+(ub-1)*(qa+s.Rational(1,12))
    target+=(pa+s.Rational(1,2))*(pb+s.Rational(1,2))
    check('Rectangular local-kernel identity',rect-target)
    out={'status':'passed','sympy_version':s.__version__,'checks':checks,'count':len(checks),'qualification':'Exact finite algebra; analytic convergence and continuation are proved in the accompanying text.'}
    output=Path(__file__).resolve().parent/'generated_results'
    output.mkdir(exist_ok=True)
    (output/'fifth_exact.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(out,indent=2))


if __name__ == '__main__':
    main()
