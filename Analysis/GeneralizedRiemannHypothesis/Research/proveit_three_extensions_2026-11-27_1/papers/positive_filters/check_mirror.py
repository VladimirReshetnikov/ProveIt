#!/usr/bin/env python3
"""Independent exact identities and high-precision checks for mirror_normal_form.tex.

The numerical checks illustrate a proved asymptotic; they are not a proof of
global optimality.  Python dependencies: mpmath and sympy.
"""
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 80
out = {}
z, y, aa = sp.symbols("z y a", nonzero=True)
roots = [-2*aa, -aa, 3*aa]
zr = [-sp.Rational(1,4), -sp.Rational(1,2), -sp.Integer(8)]
P = sp.prod(y-r for r in roots).expand()
A = sp.prod(z-r for r in zr).expand()
ac = [A.coeff(z,k) for k in range(4)]
vel = []
Rpolys = []
for V in [y, sp.Integer(1)]:
    R = sp.expand(sum(q*V.subs(y,r)/sp.diff(P,y).subs(y,r)
                      *sp.div(A,z-q,z)[0] for r,q in zip(roots,zr)))
    assert R.subs(z,0) == 0
    assert sp.degree(R,z) <= 2
    for r,q in zip(roots,zr):
        assert sp.simplify(R.subs(z,q)-q*sp.diff(A,z).subs(z,q)
                           *V.subs(y,r)/sp.diff(P,y).subs(y,r)) == 0
    Rpolys.append(str(sp.factor(R)))
    vel.append([sp.simplify(sp.pi*R.coeff(z,k)/ac[k]) for k in range(4)])

# Remove the powers pi/a and pi/a^2 from the two velocity vectors.
u = [[sp.simplify(x*aa**(j+1)/sp.pi) for x in vec]
     for j,vec in enumerate(vel)]
exact_integrals = {}
for r in range(2):
    for t in range(r,2):
        f = sp.cancel(sum(ac[j]*ac[k]*(u[r][j]-u[r][k])*(u[t][j]-u[t][k])
                          *z**(j+k-1) for j in range(4) for k in range(j+1,4))/A**2)
        F = sp.integrate(f,z)
        integ = sp.simplify(sp.limit(F,z,sp.oo)-F.subs(z,0))
        exact_integrals[f"{r+2},{t+2}"] = str(integ)
        if (r,t)==(0,1):
            expected = -sp.Rational(27,200)+sp.Rational(29441,155000)*sp.log(2)
            assert sp.simplify(integ-expected)==0
            assert -sp.Rational(27,200)+sp.Rational(29441,155000)*sp.Rational(7,10)<0

a = mp.log(2)/mp.pi
base_y = [-2*a,-a,3*a]
aco = [mp.mpf(1),mp.mpf(49)/8,mp.mpf(35)/4,mp.mpf(1)]
w0 = [x/sum(aco) for x in aco]
sig = [[mp.mpf(0),-173*mp.pi/(980*a),-7*mp.pi/(50*a),mp.mpf(0)],
       [mp.mpf(0),mp.pi/(20*a*a),-13*mp.pi/(350*a*a),mp.mpf(0)]]
def Aval(zz):
    return sum(aco[k]*zz**k for k in range(4))
Q = mp.matrix(2)
for r in range(2):
    for t in range(2):
        Q[r,t] = mp.fsum(aco[j]*aco[k]*(sig[r][j]-sig[r][k])*(sig[t][j]-sig[t][k])
                          /mp.pi*mp.quad(lambda zz,j=j,k=k: zz**(j+k-1)/Aval(zz)**2,
                                         [0,mp.mpf('0.25'),mp.mpf('0.5'),1,8,mp.inf])
                          for j in range(4) for k in range(j+1,4))
assert Q[0,0]>0 and mp.det(Q)>0 and Q[0,1]<0

checks=[]
for direction in [(1,0),(0,1),(1,1)]:
    v2,v3=direction
    prediction = (mp.matrix(direction).T*Q*mp.matrix(direction))[0]
    for eps_text in ['0.001','0.0001','0.00001']:
        eps = mp.mpf(eps_text)
        def Pc(yy):
            return yy**3-7*a*a*yy-6*a**3+1j*eps*(v2*yy+v3)
        yy = [mp.findroot(Pc,r,solver='newton',tol=mp.mpf('1e-75')) for r in base_y]
        ss = [1j+r for r in yy]
        def equations(*unknown):
            ww=list(unknown[:4]); tt=[mp.mpf(0)]+list(unknown[4:])
            f=[sum(ww)-1]
            for s in ss:
                value=mp.fsum(ww[j]*mp.exp(s*tt[j]) for j in range(4))
                f.extend([value.real,value.imag])
            return f
        sol=mp.findroot(equations,tuple(w0+[mp.pi,2*mp.pi,3*mp.pi]),
                        tol=mp.mpf('1e-65'),maxsteps=100)
        excess=sol[6]-3*mp.pi
        residual=max(abs(x) for x in equations(*sol))
        assert residual<mp.mpf('1e-60')
        assert min(sol[:4])>0
        ratio=excess/(eps*eps*prediction)
        assert abs(ratio-1)<mp.mpf('0.03')
        checks.append({'direction':direction,'epsilon':eps_text,
                       'predicted_quadratic_coefficient':mp.nstr(prediction,35),
                       'computed_scaled_excess':mp.nstr(excess/(eps*eps),35),
                       'ratio':mp.nstr(ratio,30),
                       'maximum_moment_residual':mp.nstr(residual,8)})

two_mode_checks=[]
for tt in ['0.02','0.01','0.005']:
    t=mp.mpf(tt)
    ss=[t+1j*(1+t),-t+1j*(1-t)]
    def two_equations(w0,w1,w2,t1,t2):
        ww=[w0,w1,w2];times=[mp.mpf(0),t1,t2]
        ff=[sum(ww)-1]
        for target in ss:
            val=mp.fsum(w*mp.exp(target*x) for w,x in zip(ww,times))
            ff.extend([val.real,val.imag])
        return ff
    sol=mp.findroot(two_equations,(mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf('0.25'),
                                  mp.pi,2*mp.pi),tol=mp.mpf('1e-65'))
    ratio=(sol[4]-2*mp.pi)/(4*mp.pi**3/3*t**4)
    assert abs(ratio-1)<mp.mpf('1e-5')
    two_mode_checks.append({'beta_equals_delta':tt,'ratio_to_quartic_prediction':mp.nstr(ratio,30)})

out={'precision_decimal_digits':mp.mp.dps,
     'base_polynomial':str(P),'exponential_polynomial':str(A),
     'interpolation_polynomials':Rpolys,
     'exact_normalized_integrals':exact_integrals,
     'quadratic_matrix':[[mp.nstr(Q[r,t],35) for t in range(2)] for r in range(2)],
     'finite_difference_checks':checks,
     'two_mode_quartic_checks':two_mode_checks,
     'all_checks_passed':True}
path=Path(__file__).with_name('mirror_checks.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
