"""Finite Gaussian-moment generator of the report.

The function accepts finite exact analytic data and computes a selected fixed
order. The executable example computes and checks P0 and P1 only. No explicit
P2 formula or experimental higher coefficient is supplied.
"""
import sympy as s

def transfer_coefficients(order, alpha):
    """Gamma(n-alpha)/Gamma(n+1) after its leading power n^(-alpha-1)."""
    v=s.symbols('v')
    exponent=sum((-1)**(j+1)*(s.bernoulli(j+1,-alpha)-s.bernoulli(j+1,1))*v**j/(j*(j+1)) for j in range(1,order+1))
    return s.series(s.exp(exponent),v,0,order+1).removeO().expand()

def finite_generator(order, lam, T, pressure, amplitudes):
    """Return [P0,...,P_order] for supplied f_r and H_j/C0 Taylor data.

    pressure maps r to exact f_r, including r=3.
    amplitudes maps (j,d) to [t^d](H_j(t)/C0).
    Entries needed by the finite formula must be supplied, including zeros.
    """
    if not isinstance(order, int) or order < 0:
        raise ValueError('order must be a nonnegative fixed integer')
    w, x = s.symbols('w x', real=True)
    top = 2*order
    trunc = lambda z: s.series(z,w,0,top+1).removeO().expand()
    phase = sum(2*lam*(s.I*x/2)**r*w**(r-2)/s.factorial(r) for r in range(3,top+3))
    phase += sum(pressure[3]*T**3*(3*s.I*x/4)**r*w**r/s.factorial(r) for r in range(1,top+1))
    for r in range(4,order+4):
        phase += pressure[r]*T**r*w**(2*r-6)*sum((r*s.I*x/4)**q*w**q/s.factorial(q) for q in range(top-(2*r-6)+1))
    amplitude = 0
    for j in range(order+1):
        for degree in range(order-j+1):
            value = amplitudes[(j,degree)]
            base = 2*j+2*degree
            amplitude += value*T**(degree-2*j)*w**base*sum((s.I*x*(degree/ s.Integer(4)-j/s.Integer(2)))**q*w**q/s.factorial(q) for q in range(top-base+1))
    factorial_log = sum(s.bernoulli(2*r)*w**(4*r-2)/(2*r*(2*r-1)*(2*lam)**(2*r-1)) for r in range(1,order+2) if 4*r-2<=top)
    integrand = trunc(trunc(s.exp(factorial_log))*trunc(amplitude)*trunc(s.exp(phase)))
    out=[]
    for m in range(order+1):
        poly=s.Poly(integrand.coeff(w,2*m),x)
        mean=0
        for (degree,),value in poly.terms():
            if degree%2==0:
                mean += value*s.factorial2(degree-1)*(2/lam)**(degree//2)
        out.append(s.simplify(mean))
    # Odd powers must integrate to zero, including all available phase terms.
    for power in range(1,top+1,2):
        poly=s.Poly(integrand.coeff(w,power),x)
        assert all(degree%2 or value==0 for (degree,),value in poly.terms())
    return out

if __name__=='__main__':
    lam,g,E=s.symbols('lambda gamma E',positive=True)
    # Products f3*T^3=-2 gamma lambda^(3/2), f4*T^4=E lambda^2.
    # T can be set to one after the products have been absorbed into the data.
    coefficients=finite_generator(1,lam,s.Integer(1),
        {3:-2*g*lam**s.Rational(3,2),4:E*lam**2},
        {(0,0):s.Integer(1),(0,1):-g*s.sqrt(lam)/8,(1,0):s.Integer(0)})
    assert coefficients[0]==1
    expected=g*s.sqrt(lam)/4+(E-9*g*g/4)*lam**2
    assert s.simplify(coefficients[1]-expected)==0
    print('Finite generator PASS through P1; odd Gaussian coefficients vanish.')
    print('P0 =',coefficients[0])
    print('P1 =',coefficients[1])
    v=s.symbols('v')
    for alpha in (s.Rational(1,2),s.Rational(3,2),s.Rational(5,2)):
        Q=transfer_coefficients(3,alpha)
        residual=s.series((1+v)**(-alpha-1)*Q.subs(v,v/(1+v))-(1-alpha*v)/(1+v)*Q,v,0,5)
        assert residual.removeO()==0
    assert transfer_coefficients(3,s.Rational(1,2))==1+3*v/8+25*v**2/128+105*v**3/1024
    print('Gamma-ratio Bernoulli coefficients pass the exact ratio recurrence.')
    print('No explicit higher crossover coefficient computed.')
