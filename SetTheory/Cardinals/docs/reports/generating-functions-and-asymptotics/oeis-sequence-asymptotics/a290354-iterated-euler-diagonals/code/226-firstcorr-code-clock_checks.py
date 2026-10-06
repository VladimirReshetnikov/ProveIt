#!/usr/bin/env python3
"""Exact finite symbolic checks for Report 226 (SymPy required).

These tests check finite algebra and asymptotic coefficient identities, not
analytic remainder bounds, uniformity, sector selection, or an all-order theorem.
No check uses assert, so python -O does not disable checks. JSON is emitted to
stdout; --out exclusively creates a new file. No global settings are changed.
"""
import argparse
import json
from pathlib import Path
import sympy as S


def run():
    results = []

    def zero(name, expression):
        residual = S.factor(expression)
        if residual != 0:
            raise ArithmeticError('symbolic check failed: ' + name + ': ' + str(residual))
        results.append(name)

    z, y, t, h, j, l, m, mu = S.symbols('z y t h j l m mu')
    R = S.Rational

    def coefficient(expression, k):
        return S.expand(expression).coeff(z, k)

    def truncate(expression, degree):
        return S.series(expression, z, 0, degree + 1).removeO().expand()

    # Re-derive [q^k] F_h, k<=4, directly from the Euler exponential.
    F = z + h*z**2 + h*(h+1)*z**3/2 + h*(h+1)*(2*h+1)*z**4/6
    exponent = truncate(sum(F.subs(z, z**a)/a for a in range(1, 5)), 4)
    next_F = truncate(sum(exponent**a/S.factorial(a) for a in range(1, 5)), 4)
    zero('Euler coefficients through degree four', next_F - F.subs(h, h+1))
    zero('Euler initial condition', F.subs(h, 0) - z)

    # Degree-eight h^3 contributes at scaled degree five: substitute first.
    subsidiary = truncate(sum(F.subs(z, z**a)/a for a in range(2, 6)), 8)
    forcing = truncate(subsidiary.subs(h, t/z), 5)
    proposed = (z**2/2 + z**3*(R(1, 3)+t/2) + z**4*(R(1, 4)+t*t/4)
                + z**5*(R(1, 5)+7*t/12+t**3/6))
    zero('Scaled forcing through fifth order', forcing - proposed)
    exponent = z*y + forcing
    step = truncate(sum(exponent**a/S.factorial(a) for a in range(1, 6))-z*y, 5)/z
    A, B, C, D = [coefficient(step, k) for k in range(1, 5)]
    zero('Riccati step', A-(1+y*y)/2)
    zero('Cubic scaled step', B-(y**3/6+y/2+R(1, 3)+t/2))
    zero('Quartic scaled step', C-(y**4/24+y*y/4+y/3+y*t/2+R(3, 8)+t*t/4))
    zero('Quintic scaled step', D-(y**5/120+y**3/12+y*y/6+y*y*t/4
                                  +3*y/8+y*t*t/4+R(11, 30)+5*t/6+t**3/6))

    # Symbols j,l,m represent J,L,M. Differentiate along their defining ODEs.
    den = 1+y*y
    jp = 2/den
    lp = (y**3/3-y-R(4, 3)-2*j)/den**2

    def derivative(expression, mp=mu):
        return (S.diff(expression, y)+jp*S.diff(expression, j)
                +lp*S.diff(expression, l)+mp*S.diff(expression, m))

    j2, j3, j4 = [S.diff(jp, y, a) for a in (1, 2, 3)]
    l2 = derivative(lp)
    l3 = derivative(l2)
    first = jp*B+j2*A*A/2+lp*A
    zero('First clock cancellation', first-(t-j)/den)
    second = jp*C+j2*A*B+j3*A**3/6+lp*B+l2*A*A/2+mu*A
    mp = S.factor(S.solve(second.subs(t, j)+l/den, mu)[0])
    mp_explicit = -(36*j*j*(y*y-1)+12*j*(5*y**3-3*y-8)+72*l*den
                    +y**6+9*y**4+40*y**3-21*y*y-24*y-29)/(36*den**3)
    zero('M differential equation', mp-mp_explicit)
    zero('M cancels the self-consistent second coefficient', second.subs({t:j, mu:mp})+l/den)
    m2 = derivative(mp, mp)
    third = (jp*D+j2*(A*C+B*B/2)+j3*A*A*B/2+j4*A**4/24
             +lp*C+l2*A*B+l3*A**3/6+mp*B+m2*A*A/2)
    G = S.factor(third.subs(t, j)+l*S.diff(second, t).subs(t, j)+m/den)
    np = -G/A
    zero('Time derivative of Q2', S.diff(second, t).subs(t, j)-(j/den+lp/2))

    # Independently compose the step with t=J+zL+z^2M+z^3N.
    n = S.symbols('n')
    b = B.subs(t, j)
    c = C.subs(t, j)+l/2
    d = D.subs(t, j)+(y+j)*l/2+m/2
    direct_G = (jp*d+j2*(A*c+b*b/2)+j3*A*A*b/2+j4*A**4/24
                +lp*c+l2*A*b+l3*A**3/6+mp*b+m2*A*A/2)
    zero('Two independent G3 specifications agree', direct_G-G)
    zero('N cancels self-consistent third coefficient', direct_G+A*np)

    # x=1/y: finite power-log coefficient tests, not remainder certificates.
    x, T, Bc, kap = S.symbols('x T Bc kappa', positive=True)
    Jx = T-2*x+2*x**3/3-2*x**5/5
    Lx = -S.log(x)/3+Bc+R(5, 6)*x*x+(R(4, 9)+2*T/3)*x**3-R(7, 4)*x**4
    Mx = (-1/(36*x)+kap+x/6+(5*T/6+R(5, 9))*x*x
          +(-R(2, 9)*S.log(x)+2*Bc/3+T*T/3-R(77, 54))*x**3)
    zero('J asymptotic coefficients', S.series(-x*x*S.diff(Jx,x)-jp.subs(y,1/x),x,0,7).removeO())
    lps = lp.subs({y:1/x,j:Jx})
    zero('L asymptotic coefficients through inverse fourth power',
         S.series(-x*x*S.diff(Lx,x)-lps,x,0,6).removeO())
    mps = S.series(mp.subs({y:1/x,j:Jx,l:Lx}), x, 0, 5).removeO()
    zero('M asymptotic coefficients through log over y cubed',
         S.series(-x*x*S.diff(Mx,x)-mps,x,0,5).removeO())
    gs = S.series(G.subs({y:1/x,j:Jx,l:Lx,m:Mx}),x,0,2).removeO()
    expected_G = (-1/(540*x**3)-1/(360*x)+T/12+R(1,18)
                  +x*(-R(5,18)*S.log(x)+5*Bc/6+5*T*T/12-R(3,20)))
    zero('G3 asymptotic coefficients through inverse y', gs-expected_G)
    ns = S.series(np.subs({y:1/x,j:Jx,l:Lx,m:Mx}),x,0,4).removeO()
    Ntail = (1/(540*x*x)-S.log(x)/540+(T/6+R(1,9))*x
             +x*x*(-R(5,18)*S.log(x)+5*Bc/6+5*T*T/12-R(11,1080)))
    zero('N asymptotic coefficients including logarithmic resonance',
         S.series(-x*x*S.diff(Ntail,x)-ns,x,0,4).removeO())

    # Exact L primitive and kappa evaluation. The two classical log-cos
    # integral identities below are analytic inputs stated in the report.
    u, lc = S.symbols('u lc', real=True)
    cos2 = (1-y*y)/den
    sin2 = 2*y/den
    cos4 = (1-6*y*y+y**4)/den**2
    sin4 = 4*y*(1-y*y)/den**2
    Lu = (-lc/3+R(1,3)-cos2/6+(T-R(2,3))*u-u*u
          +(T/2-R(1,3)-u)*sin2-S.log(2)/6-T*T/4+T/3)
    Lu_derivative = S.diff(Lu,y)+S.diff(Lu,u)/den-S.diff(Lu,lc)*y/den
    zero('L primitive derivative', Lu_derivative-lp.subs(j,2*u-T))
    zero('L primitive normalization', Lu.subs({y:1,u:T/2,lc:-S.log(2)/2}))
    p0 = 2*u*u-2*T*u+T*T/2+8*u/3-4*T/3+R(1,12)+S.log(2)/6
    p2 = 3*u*u-3*T*u+3*T*T/4+10*u/3-5*T/3+R(1,3)+S.log(2)/6
    p4 = u*u-T*u+T*T/4+2*u/3-T/3+R(1,12)
    q2 = 2*u/3-T/3+R(2,9)
    q4 = 7*u/6-7*T/12+R(7,18)
    poly = p0+p2*cos2+p4*cos4+q2*sin2+q4*sin4
    zero('Exact transformed kappa integrand',
         (mp+R(1,36)).subs({j:2*u-T,l:Lu})*den-(R(2,3)*lc/den+poly))
    trig_poly = p0+p2*S.cos(2*u)+p4*S.cos(4*u)+q2*S.sin(2*u)+q4*S.sin(4*u)
    poly_integral = S.simplify(S.integrate(trig_poly.subs(T,S.pi/2),(u,S.pi/4,S.pi/2)))
    log_integral = -S.pi*S.log(2)/4-S.Catalan/2
    cos_log_integral = S.log(2)/4+S.pi/8+R(1,4)
    derived_kappa = S.expand(R(1,36)+poly_integral+(log_integral+cos_log_integral)/3)
    claimed_kappa = S.pi**3/96+S.pi**2/12-13*S.pi/48-R(11,36)-S.Catalan/6-S.pi*S.log(2)/24
    zero('Kappa closed form from stated classical integrals', derived_kappa-claimed_kappa)

    # Autonomous Abel equation and the forced cohomological correction.
    w, a1, a2, a3 = S.symbols('w a1 a2 a3')
    f = S.exp(w)-1
    phi = -2/w+S.log(w)/3+a1*w+a2*w*w+a3*w**3
    defect = S.series(phi.subs(w,f)-phi-1,w,0,5).removeO().expand()
    solution = S.solve([defect.coeff(w,k) for k in (2,3,4)],(a1,a2,a3))
    for name, symbol, value in [('a1',a1,-R(1,36)),('a2',a2,R(1,540)),('a3',a3,R(1,7776))]:
        zero('Fatou coefficient '+name,solution[symbol]-value)
    phi = phi.subs(solution)
    U = 2/(3*w**3)+5/(6*w*w)+1/(6*w)
    cohomology = S.series(U.subs(w,f)-U+S.diff(phi,w)/2,w,0,2).removeO()
    zero('Forced Fatou cohomology including constant and linear terms',cohomology+w/1080)

    # Exponential parameter and inverse-transform polynomial algebra.
    e, s, dd, k = S.symbols('e s d kappa')
    phase = (1/e-(1/e+dd)*S.exp(-s*e)+dd-S.log(1+dd*e)/3
             +s*e/3-k*T*e*S.exp(s*e)/(1+dd*e))
    Q = (dd+R(1,3))*s-s*s/2-dd/3-k*T
    zero('Exponential phase polynomial',S.series(phase,e,0,2).removeO()-s-e*Q)
    q = S.symbols('q',integer=True,positive=True)
    xx = S.symbols('xx',positive=True)
    hx = S.Function('h')(xx)
    inv_s = (-S.diff(xx**(q+1)*hx,xx)+q*xx**q*hx)/xx**q
    inv_s2 = (S.diff(xx**(q+1)*hx,xx,2)-2*q*S.diff(xx**q*hx,xx)
              +q*(q-1)*xx**(q-1)*hx)/xx**q
    zero('Inverse of derivative-q of s P prime',S.simplify(inv_s+hx+xx*S.diff(hx,xx)))
    zero('Inverse of derivative-q of s squared P prime',S.simplify(inv_s2-2*S.diff(hx,xx)-xx*S.diff(hx,xx,2)))
    r1, r2, ell, d0 = S.symbols('rho1 rho2 ell d0')
    diagonal_poly = -dd**2/2-dd*(R(4,3)+r1)-k*T-R(1,3)-4*r1/3-r2/2
    log_poly = S.expand(diagonal_poly.subs(dd,-ell/3+d0))
    zero('Diagonal squared-log coefficient',log_poly.coeff(ell,2)+R(1,18))
    zero('Diagonal log coefficient',log_poly.coeff(ell,1)-(d0/3+R(4,9)+r1/3))
    zero('Diagonal constant coefficient',log_poly.coeff(ell,0)-(-d0*d0/2-d0*(R(4,3)+r1)-k*T-R(1,3)-4*r1/3-r2/2))

    beta = S.symbols('beta',positive=True)
    correction = ((-dd/3-k*T)*beta-(dd+R(1,3))*(1+beta*r1)
                  -r1-beta*r2/2-beta*dd*dd/2)
    height_poly = (-beta*dd*dd/2-dd*(1+beta/3+beta*r1)-beta*k*T
                   -R(1,3)-(1+beta/3)*r1-beta*r2/2)
    zero('Proportional-height polynomial',correction-height_poly)
    zero('Proportional height beta one',height_poly.subs(beta,1)-diagonal_poly)
    zero('Proportional-height squared-log coefficient',S.expand(height_poly.subs(dd,-ell/3+d0)).coeff(ell,2)+beta/18)

    # Conditional inverse expansion, with q=log(X/T)+1 held as a symbol.
    v, alpha, Ulog, logc, Ac, Cc, D0, D1, qlog = S.symbols('v alpha U logc Ac Cc D0 D1 qlog')
    correction_Q = lambda value: -value*value/18+Ac*value+Cc
    increment = D0+D1*v
    residual = (qlog*increment+(1/v+increment)*S.log(1+increment*v)-increment
                -alpha*(Ulog+S.log(1+increment*v))+logc
                +v*correction_Q(Ulog+S.log(1+increment*v))/(1+increment*v))
    inverse_D0 = (alpha*Ulog-logc)/qlog
    inverse_D1 = -(inverse_D0*inverse_D0/2-alpha*inverse_D0+correction_Q(Ulog))/qlog
    zero('Conditional inverse constant and first inverse-X terms',
         S.series(residual,v,0,2).removeO().subs({D0:inverse_D0,D1:inverse_D1}))

    # Exact exponent arithmetic for the public sqrt-height matching choice.
    # Analytic bounds, including sector control, remain proofs in the article.
    Kexp, strip, local, target = R(1,2), R(1,20), R(3,2), R(7,5)
    budgets = {
        'clock and cubic Fatou remainder': 3*Kexp,
        'subsidiary matching z cubed over w cubed': 3-3*Kexp,
        'subsidiary matching z fourth over w fifth': 4-5*Kexp,
        'corrected phase z cubed reciprocal square sum': 3-3*Kexp,
        'corrected phase z fourth reciprocal fourth sum': 4-5*Kexp,
        'terminal removal': 2-3*strip,
        'degree three phase Taylor remainder': 2-3*strip,
        'degree four composition Taylor remainder': 2-4*strip,
    }
    for label, exponent in budgets.items():
        if exponent < local:
            raise ArithmeticError('local exponent budget failed: '+label)
        results.append('Exponent budget: '+label+' = '+str(exponent))
    zero('Clock matching exponent',3*Kexp-local)
    zero('Central integration exponent',local-strip-R(29,20))
    zero('Thirty derivatives tail exponent',30*strip-R(3,2))
    if not (2-3*Kexp > 0 and strip < Kexp
            and local-strip > target and 30*strip > target
            and 2 > local and 2 > target):
        raise ArithmeticError('exponent budget inequality failed')
    results.append('Exact exponent-budget inequalities for relative 7/5 remainder')
    return {'status':'passed','scope':'finite exact identities only; no analytic remainder or uniformity certificate',
            'checks':results,'check_count':len(results),'sympy_version':S.__version__,
            'kappa_exact':str(claimed_kappa),
            'analytic_inputs':['The stated two classical log-cos integral evaluations',
                               'Sectorial construction and analytic bounds in the report are not proved by these tests']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',help='optional NEW JSON file; otherwise stdout only')
    args = parser.parse_args()
    output = json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if args.out:
        with Path(args.out).open('x') as stream:
            stream.write(output)
    print(output,end='')


if __name__ == '__main__':
    main()
