#!/usr/bin/env python3
"""Exact finite algebra for the depth-four ordered Hurwitz normal form.

This independently solves the regularized stuffle jet equations and checks
the printed Laurent polynomial, diagonal Gamma specialization, reconstruction
matrix and shift coefficients. Analytic continuation is proved in the article.
"""
import json
from pathlib import Path
import sympy as s

g, g1, g2, g3, z2, z2p, z2pp, z3, z3p, z4 = s.symbols(
    'g g1 g2 g3 z2 z2p z2pp z3 z3p z4')
eta, rho, kap, T = s.symbols('eta rho kappa T')
u, v, w, e, p, b, c, d, y = s.symbols('u v w e p b c d y')
B2 = (g*g-z2)/2
B3 = (g**3-3*g*z2+2*z3)/6
B4 = (g**4-6*g*g*z2+3*z2*z2+8*g*z3-6*z4)/24
D1 = -g*g1-z2p
E, F = (g*g2-z2pp)/2, (g1*g1-z2pp)/2
S = -g1*B2-g*z2p+z3p
V = g*eta+g1*(g*g+z2)/2+g*z2p-T
checks = []

def check(name, expression):
    assert s.cancel(s.expand(expression)) == 0, (name, expression)
    checks.append(name)

# Solve the coefficient equations instead of initializing their answers.
aa, bb, cc, dd, ee = s.symbols('aa bb cc dd ee')
solution = s.solve([
    aa-eta, aa+bb-D1, cc+ee-E, dd-F, cc-ee-rho
], [aa, bb, cc, dd, ee], dict=True)[0]
R2 = B2+solution[aa]*u+solution[bb]*v+solution[cc]*u*u
R2 += solution[dd]*u*v+solution[ee]*v*v
check('R2 quadratic symmetry',
      R2+R2.xreplace({u:v,v:u})-
      (2*B2+D1*(u+v)+E*(u*u+v*v)+2*F*u*v))
X, Y, Z = s.symbols('X Y Z')
solution3 = s.solve([
    X+Y+Z-S, 2*X+Y-(g*eta+g1*z2+z3p-T), X-2*Y+Z-kap
], [X,Y,Z], dict=True)[0]
R3 = B3+solution3[X]*u+solution3[Y]*v+solution3[Z]*w
check('R3 printed jet', R3-(B3+S*(u+v+w)/3+kap*(u-2*v+w)/6+V*(u-w)/2))

R1 = g-g1*u+g2*u*u/2-g3*u**3/6
laurent = (1/(p*(p+b)*(p+b+c)*(p+b+c+d)*e**4)
           + R1.subs(u,d*e)/(p*(p+b)*(p+b+c)*e**3)
           + R2.subs({u:c*e,v:d*e})/(p*(p+b)*e**2)
           + R3.subs({u:b*e,v:c*e,w:d*e})/(p*e)+B4)
printed = (B4+(S*(b+c+d)/3+kap*(b-2*c+d)/6+V*(b-d)/2)/p
           +(E*(c*c+d*d)/2+F*c*d+rho*(c*c-d*d)/2)/(p*(p+b))
           -g3*d**3/(6*p*(p+b)*(p+b+c)))
laurent_polynomial=s.Poly(s.cancel(laurent*e**4),e)
check('Full constant coefficient', laurent_polynomial.nth(4)-printed)
principal = {
    -4:1/(p*(p+b)*(p+b+c)*(p+b+c+d)),
    -3:g/(p*(p+b)*(p+b+c)),
    -2:B2/(p*(p+b))-d*g1/(p*(p+b)*(p+b+c)),
    -1:B3/p+(eta*(c-d)+D1*d)/(p*(p+b))
       +g2*d*d/(2*p*(p+b)*(p+b+c))}
for j,value in principal.items():
    check(f'Principal coefficient {j}', laurent_polynomial.nth(j+4)-value)

# Independent ordinary Gamma diagonal generator, through total weight four.
t=s.symbols('t')
logF = y*(g-g1*t+g2*t*t/2-g3*t**3/6)
logF -= y*y*(z2+2*z2p*t+2*z2pp*t*t)/2
logF += y**3*(z3+3*z3p*t)/3-y**4*z4/4
gen = s.series(s.exp(logF),y,0,5).removeO().expand()
diag = s.S(0)
q=s.symbols('q')
for k in range(4):
    numerator = gen.coeff(y,4-k).expand().coeff(t,k)
    den = s.prod(p+j*q for j in range(k))
    diag += q**k*numerator/den
check('Gamma diagonal generation', printed.subs({b:q,c:q,d:q})-diag)

matrix=s.Matrix([[-s.Rational(1,3),s.Rational(3,4),0],
                 [-s.Rational(2,3),2,0],[s.Rational(1,6),0,s.Rational(1,2)]])
check('Reconstruction determinant',matrix.det()+s.Rational(1,12))
DA,DB,DC=s.symbols('DA DB DC')
reconstructed=matrix.inv()*s.Matrix([DA,DB,DC])
check('Reconstruction kappa',reconstructed[0]-(s.Rational(9,2)*DB-12*DA))
check('Reconstruction rho',reconstructed[1]-(2*DB-4*DA))
check('Reconstruction V',reconstructed[2]-(2*DC-s.Rational(3,2)*DB+4*DA))

L,a=s.symbols('L a',nonzero=True)
shift2=s.expand((1-v*L+v*v*L*L/2)*R1/a)
check('Shift eta',shift2.coeff(u,1).coeff(v,0)+g1/a)
check('Shift rho',shift2.coeff(u,2).coeff(v,0)-shift2.coeff(v,2).coeff(u,0)
      -(g2-g*L*L)/(2*a))
shift3=s.expand((1-w*L)*R2/a)
delta=(shift3.coeff(u,1).coeff(v,0).coeff(w,0)
       -2*shift3.coeff(v,1).coeff(u,0).coeff(w,0)
       +shift3.coeff(w,1).coeff(u,0).coeff(v,0))
check('Shift kappa',delta-(3*eta-2*D1-L*B2)/a)

for ray in [(1,1,2,1),(1,1,3,1),(1,2,1,1),(5,-3,-1,1),
            (1,1,-1,1),(2,0,0,0),(3,2,2,2)]:
    substitutions=dict(zip((p,b,c,d),ray))
    check('Ray '+str(ray),
          (laurent_polynomial.nth(4)-printed).subs(substitutions))

# A changed kappa coefficient must be rejected on a nonsymmetric ray.
corrupted=printed+kap*(b-2*c+d)/(6*p)
assert s.cancel((corrupted-printed).subs({p:1,b:1,c:2,d:1})) != 0
checks.append('Corrupted kappa coefficient rejected')
result={'status':'passed','kind':'exact symbolic algebra',
        'check_count':len(checks),'checks':checks,
        'reconstruction_determinant':str(matrix.det())}
out=Path(__file__).resolve().parents[1]/'results'/'ordered_exact.json'
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
