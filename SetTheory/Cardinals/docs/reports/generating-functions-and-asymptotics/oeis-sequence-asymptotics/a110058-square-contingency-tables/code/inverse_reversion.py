"""Fixed-order exact formal reversion; no numerical root certificate.

The computation treats a,b,L as independent symbolic quantities. Analytically
L=log(r), a=log(4), b=log(4*pi). It verifies coefficients only; remainder
estimates and inversion of the discrete counting sequence belong to the article.
"""
import sympy as s
from common import require


def check_reversion():
    t,a,b,L=s.symbols('t a b L', nonzero=True)
    D,E,F,G=s.symbols('D E F G')
    c1,c2=s.symbols('C1 C2')
    d=(L+b)/(2*a)
    e=(a*d*d+d-L-b/2-s.Rational(1,4))/(2*a)
    f=(e-d+d*d/2-c1)/(2*a)
    g=(f-a*e*e+d*e-d**3/6-e+d*d/2+c1*d-c2)/(2*a)
    h=D*t+E*t**2+F*t**3+G*t**4
    x=1/t+D+E*t+F*t**2+G*t**3
    # Enough formal terms to capture every coefficient from t^-1 to t^2.
    log_poly=sum((-1)**(k+1)*h**k/s.Integer(k) for k in range(1,5))
    expression=s.expand(a*x*x-x*(L+log_poly)-b*x+L+log_poly+b/2+s.Rational(1,4)
                        +c1*t*(1-h+h*h)+c2*t*t-a/t**2)
    rows=[]
    values={D:d,E:e,F:f,G:g}
    for power in (-1,0,1,2):
        coefficient=expression.coeff(t,power)
        verified=s.cancel(coefficient.subs(values))
        require(verified==0,'formal inverse coefficient mismatch')
        rows.append({'power_of_t':power,'residual_before_substitution':str(coefficient),
                     'residual_after_substitution':'0'})
    return {'status':'PASS','checked_residual_coefficients':rows,
            'a':'log(4)','b':'log(4*pi)','L':'log(r)','t':'1/r',
            'C1_and_C2_are_formal_indeterminates':True,
            'density_one_specialization':{'C1':'-3/2','C2':'223/32'},
            'scope':'Exact formal cancellation only; not an analytic error bound or a certified numerical inverse.'}
