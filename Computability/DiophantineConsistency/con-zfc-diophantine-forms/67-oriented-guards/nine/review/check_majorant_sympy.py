#!/usr/bin/env python3
"""Independent exact symbolic audit using SymPy, no constructor imports."""
import json
import sympy as s
D,e,A,C,i,H=s.symbols('D e A C i H')
L=C*D+1-A;F=(D-1)*D**2*e**2+1;G=A+F*L;N=2*G+L;X=e**2*D**3*(D-1)
Ns=[2*e**2*D*(D-1)*L+3*C,2*e**2*(D-1)*L,2*e**2*(L-C),2*e**2*C]
rs=[3-A,3*C*D+3-A]
rs += [2*e**2*(A-1)*D**2+rs[1],2*e**2*(1-A-C)*D**3+2*e**2*(A-1)*D**2+rs[1]]
for j in range(4):
 if s.expand(N-D**(j+1)*Ns[j]-rs[j])!=0:raise ValueError('remainder')
checks=[]
for r,scale in enumerate([128,64,8,4,1]):
 lam=s.Rational(2048,scale);cs=[s.Rational(x,scale) for x in [64,40,28,21]]
 tn=(1024*D**6-512*D**5-128*D**4)/scale-sum(cs[j]*D**(3-j) for j in range(r))
 defect=s.Poly(s.expand(tn**2-(1024//scale)**2*D**11*(D-1)),D)
 if not (all(c>=0 for c in defect.all_coeffs()) and defect.LC()>0):raise ValueError('positive defect coefficients')
 cor=256*i*(e**2+2)+2048 if r==4 else 512//scale*i+lam if r else lam
 T=e*((1024*D**2-512*D-128)/scale*N-sum(cs[j]*Ns[j] for j in range(r)))+cor
 rn=e*sum(cs[j]*rs[j]*D**(3-j) for j in range(r))+cor*D**4
 if s.expand(D**4*T-e*tn*N-rn)!=0:raise ValueError('truncation identity')
 rhs=e**2*defect.as_expr()*N**2+(1024//scale)**2*D**8*(X*L**2-4*D*G*(C*D+1))+2*e*tn*N*rn+rn**2
 if s.expand(D**8*(T*T-lam**2*D*F*G*G)-rhs)!=0:raise ValueError('cancellation identity')
 checks.append({'order':r,'defect_degree':defect.degree(),'defect_coefficients':[int(c) for c in defect.all_coeffs()]})
a,b,v,w,o,z=s.symbols('a b v w o z')
d0=v*v-a;d1=w*w-b;small=z*z-2*z*o*(v+w)+o*o*(d0+d1)
norm=((z-o*(v+w))**2-o*o*(a+b))**2-4*o**4*a*b
expanded=small**2+4*o*o*v*w*small+4*o**4*(d0*w*w+a*d1)
if s.expand(norm-expanded)!=0:raise ValueError('norm decomposition')
print(json.dumps({'status':'PASS','independent_engine':'SymPy '+s.__version__,'remainders':4,'norm_identity':True,'orders':checks},indent=2))
