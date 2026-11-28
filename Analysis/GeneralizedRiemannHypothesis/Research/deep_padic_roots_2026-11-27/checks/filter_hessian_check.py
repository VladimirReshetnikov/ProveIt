#!/usr/bin/env python3
"""Exact algebra and numerical checks of the arbitrary mirror Hessian notes.

The exact identities are independently checked by SymPy. Numerical roots of
the moment equations illustrate the proven expansion; they are not interval
certificates and are not used as proof of global optimality.
"""
import json
import sympy as sp
import mpmath as mp

z, c = sp.symbols('z c', real=True)
A = 1 + 2*c
P = (z + 1)*(z*z + 2*c*z + 1)
R = (A*(z+z*z)*P - A*A*(z-z*z)**2)/(z*P*P)
partial = c*(c-4)*A/((c-1)**2*(z*z+2*c*z+1))
partial -= z*(c+1)*A*A/((c-1)*(z*z+2*c*z+1)**2)
partial += A*A/((c-1)**2*(z+1)**2)
assert sp.cancel(R-partial) == 0
R_half = sp.cancel(R.subs(c, 0))
assert sp.cancel(R_half - (1/(z+1)**2 + z/(z*z+1)**2)) == 0

# Integral simplification; J denotes arccos(c)/sqrt(1-c*c).
J = sp.symbols('J', real=True)
integral_R = c*(c-4)*A*J/(c-1)**2
integral_R -= (c+1)*A*A*(1-c*J)/(2*(c-1)*(1-c*c))
integral_R += A*A/(c-1)**2
Q = sp.cancel(4*sp.pi*(1-c)**2/A**2*integral_R)
assert sp.cancel(Q - 6*sp.pi*(1-3*c*J/A)) == 0

x = sp.symbols('x', positive=True)
Qx = 6*sp.pi*(1-3*x*sp.cos(x)/((1+2*sp.cos(x))*sp.sin(x)))
coalescence_series = sp.series(Qx, x, 0, 8)
assert sp.simplify(sp.limit((2*sp.pi/3-x)*Qx, x, 2*sp.pi/3)) == 4*sp.pi**2

mp.mp.dps = 80
data = []
for ds in ('0.25', '0.5', '0.6'):
    d = mp.mpf(ds)
    cc = mp.cos(mp.pi*d)
    aa = 1+2*cc
    predicted = 6*mp.pi*(1-3*mp.pi*d*cc/(aa*mp.sin(mp.pi*d)))
    p0 = aa/(2*(1+cc))
    for es in ('0.0001', '0.00001', '0.000001'):
        e = mp.mpf(es)
        lambdas = [1-d+e, 1-2*e, 1+d+e]
        def equations(a, b, p):
            return tuple(p*mp.cos(l*a)+(1-p)*mp.cos(l*b) for l in lambdas)
        a0 = mp.pi/2 - 2*mp.pi*(1-cc)/aa*e
        a,b,p = mp.findroot(equations, (a0,3*mp.pi/2,p0), tol=mp.mpf('1e-65'))
        assert 0<a<b and 0<p<1
        residual = max(abs(r) for r in equations(a,b,p))
        observed = (2*b-3*mp.pi)/(e*e)
        data.append({'d': ds, 'epsilon': es,
                     'Q_predicted': mp.nstr(predicted, 50),
                     'width_excess_over_epsilon_squared': mp.nstr(observed,50),
                     'ratio_to_predicted': mp.nstr(observed/predicted,40),
                     'moment_residual': mp.nstr(residual,8)})
report = {'exact_checks': ['partial fraction identity', 'd=1/2 integral identity',
                          'closed curvature simplification', 'boundary coefficient'],
          'coalescence_series_in_x_pi_times_d': str(coalescence_series),
          'numerical_checks': data,
          'limitations': 'Moment roots are floating-point illustrations, not interval certificates.'}
print(json.dumps(report, indent=2))
