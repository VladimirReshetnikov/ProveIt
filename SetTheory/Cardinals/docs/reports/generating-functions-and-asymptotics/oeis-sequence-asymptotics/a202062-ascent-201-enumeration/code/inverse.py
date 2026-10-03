#!/usr/bin/env python3
"""Exact arbitrary-order inverse coefficients and a numerical illustration.

The result approximates the specified cut-integral real model. It is not an
unqualified integer-threshold formula or a certified finite-target error bound.
"""
import argparse
from pathlib import Path
import subprocess
import sys
import sympy as s
import mpmath as mp

parser=argparse.ArgumentParser()
parser.add_argument('--order',type=int,default=5)
parser.add_argument('--target-log',default='1000',help='Natural logarithm of Y')
args=parser.parse_args()
if args.order<1:parser.error('--order must be positive')
M=args.order; HERE=Path(__file__).resolve().parent
r,L=s.symbols('r L'); D=r**3+5*r*r-8*r+1
coeffile=HERE/'relative-coefficients.txt'
if not coeffile.exists() or len(coeffile.read_text().splitlines())<=M:
    subprocess.run([sys.executable,str(HERE/'puiseux.py'),'--relative-order',str(M)],check=True,stdout=subprocess.DEVNULL)
field=s.QQ.frac_field(L); modulus=s.Poly(D,r,domain=field)
red=lambda expr:s.Poly(expr,r,domain=field).rem(modulus).as_expr()
c=[]
for line in coeffile.read_text().splitlines():
    if line:c.append(s.sympify(line.split('=',1)[1],locals={'r':r}))
ell=[s.Integer(0)]
for m in range(1,M+1):
    ell.append(red(c[m]-sum(k*ell[k]*c[m-k] for k in range(1,m))/m))
kappa=s.Rational(9,2)

def mul(a,b):
    out=[s.Integer(0)]*(M+1)
    for i in range(M+1):
        out[i]=red(sum(a[j]*b[i-j] for j in range(i+1)))
    return out

def residual(E):
    H=[s.Integer(0)]+E[:-1]
    powers=[[s.Integer(1)]+[s.Integer(0)]*M]
    for k in range(1,M+1):powers.append(mul(powers[-1],H))
    out=[L*t for t in E]
    for m in range(M+1):
        out[m]-=kappa*sum(s.Rational((-1)**(k+1),k)*powers[k][m] for k in range(1,M+1))
        for j in range(1,m+1):
            out[m]+=ell[j]*sum((-1)**k*s.binomial(j+k-1,k)*powers[k][m-j] for k in range(M+1))
        out[m]=red(out[m])
    return out

E=[s.Integer(0)]*(M+1)
for m in range(1,M+1):
    E[m]=red(-residual(E)[m]/L)
assert all(z==0 for z in residual(E))
expected=[None,-ell[1]/L]
if M>=2:expected.append(-ell[2]/L-kappa*ell[1]/L**2)
if M>=3:expected.append(-ell[3]/L-(kappa*ell[2]+ell[1]**2)/L**2-kappa**2*ell[1]/L**3)
for j in range(1,min(3,M)+1):assert red(E[j]-expected[j])==0
lines=['lambda = log(1/rho)', 'rho^3 + 5rho^2 - 8rho + 1 = 0; 0.137 < rho < 0.138']
for j in range(1,M+1):lines.append('d'+str(j)+' = '+str(s.factor(E[j])))
(HERE/'inverse-coefficients.txt').write_text('\n'.join(lines)+'\n')
print('PASS: inverse recurrence has exact zero residual through order',M)
print('PASS: displayed inverse coefficients d1 through d'+str(min(3,M))+' agree')
mp.mp.dps=70
rho=mp.mpf(str(s.CRootOf(D,1).evalf(75))); lam=mp.log(1/rho)
delta=mp.sqrt(6*rho*rho+37*rho-5)
C=105*delta*(10-11*rho-2*rho*rho)/(16*mp.sqrt(mp.pi))
logY=mp.mpf(args.target_log);kap=mp.mpf(9)/2
arg=-lam/kap*mp.exp((mp.log(C)-logY)/kap)
if arg < -1/mp.e:raise ValueError('Target is too small for the large Lambert-W branch')
n0=-kap/lam*mp.lambertw(arg,-1)
def numeric(expr):return mp.mpf(str(s.N(expr.subs({r:s.Float(str(rho),75),L:s.Float(str(lam),75)}),70)))
nu=n0+sum(numeric(E[j])/n0**j for j in range(1,M+1))
res=mp.log(C)+lam*nu-kap*mp.log(nu)+sum(numeric(ell[j])/nu**j for j in range(1,M+1))-logY
print('log(Y) =',mp.nstr(logY,30))
print('Leading n0 =',mp.nstr(n0,40))
print('Order-'+str(M)+' real inverse approximation =',mp.nstr(nu,40))
print('Truncated logarithmic-model residual =',mp.nstr(res,12))
print('No certified finite-Y rounding claim is made without explicit remainder constants.')
