"""Exact rational coefficient generator for iterated Bell diagonals.
Requires SymPy. The finite symbolic identities are checks, not analytic proofs.
"""
import argparse,json
from pathlib import Path
import sympy as s
p=argparse.ArgumentParser();p.add_argument('--order',type=int,default=3);p.add_argument('--out',default='coefficients.json');args=p.parse_args()
M=args.order
if not 1<=M<=8:raise SystemExit('Use an order between 1 and 8; high orders may be slow.')
x,y,L,b=s.symbols('x y L b')
trunc=lambda z,k:s.series(z,x,0,k).removeO().expand()
g=s.series(2/s.log(1+2*x)-1/x-1,x,0,M+3).removeO().expand()
a=[g.coeff(x,k) for k in range(1,M+2)]
q=trunc(x*(1/x+1+g),M+3)
ds=[]; bounds=[]
for j in range(1,M+1):
 d=s.symbols("d")
 defect=trunc((q-1-x)/x+s.log(q)/3+sum(ds[k-1]*x**k*(q**(-k)-1) for k in range(1,j))+d*x**j*(q**(-j)-1),j+2).coeff(x,j+1)
 value=s.solve(defect,d)[0];ds.append(value)
 assert s.simplify(defect.subs(d,value))==0
 C=s.Integer(3)**(j+2)*(s.Rational(8,15)+sum(abs(ds[k-1])*(s.Rational(3,5)**k+s.Rational(1,3)**k) for k in range(1,j+1)))
 bounds.append({"J":j,"defect_constant":str(C),"fatou_remainder_constant":str(C*(s.Rational(1,4)+s.Rational(12,11*(j+1))))})
v=[]
for j in range(1,M+1):
 cs=s.symbols('c0:'+str(j+1));V=sum(cs[k]*y**k for k in range(j+1))
 vv=v+[V]
 W=1/x+y+sum(vv[k-1]*x**k for k in range(1,j+1))
 xp=x/(1+x);yp=y-s.log(1+x)/3
 Wnext=(1+x)/x+yp+sum(vv[k-1].subs(y,yp)*xp**k for k in range(1,j+1))
 # Only finitely many reciprocal powers can affect the target coefficient.
 defect=trunc(Wnext-W-1-sum(a[k-1]*trunc((1/W)**k,j+2) for k in range(1,j+2)),j+2).coeff(x,j+1)
 solution=s.solve(s.Poly(defect,y).coeffs(),cs,dict=True)
 assert len(solution)==1
 V=s.expand(V.subs(solution[0]));v.append(V)
 assert s.Poly(V,y).degree()<=j
 assert s.expand(defect.subs(solution[0]))==0
W=1/x+y+sum(v[k-1]*x**k for k in range(1,M+1))
lognorm=trunc(s.log(W*x)/x-y,M+1)
stirling=sum(s.bernoulli(2*k)*x**(2*k-1)/(2*k*(2*k-1)) for k in range(1,(M+1)//2+1))
Rs=trunc(s.exp(lognorm+stirling),M+1)
R=[s.expand(Rs.coeff(x,j)) for j in range(M+1)]
assert R[0]==1
assert s.expand(R[1]-(-y*y/2-y/3+s.Rational(1,36)))==0
for j in range(M+1):assert s.Poly(R[j],y).degree()<=2*j
out={'order':M,'variable':'y = Psi(u) - log(n)/3; replace Psi by Psi+k for depth n+k','abel_coefficients':[str(z) for z in ds],'explicit_remainder_bounds':bounds,'remainder_meaning':'For Re(w)>=4, defect <= C_J |w|^(-J-2), and |Phi(w)-V_J(w)| <= B_J Re(w)^(-J-1).','reciprocal_iterate':[str(z) for z in v],'forward_integrand':[str(z) for z in R],'forward_in_L_and_b':[str(s.expand(z.subs(y,b-L/3))) for z in R],'assertions':'recurrence cancellation, polynomial degree, and first coefficient all passed'}
Path(args.out).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
