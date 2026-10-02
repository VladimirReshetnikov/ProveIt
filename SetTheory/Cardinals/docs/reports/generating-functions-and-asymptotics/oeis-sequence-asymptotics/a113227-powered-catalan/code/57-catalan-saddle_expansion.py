"""Exact real-saddle coefficients c_j(w), using symbolic Gaussian moments."""
import sympy as s
from residue_expansion import B,z as invk
J=4
w,z,v=s.symbols('w z v')
# alpha_l: residue relative to (2pi e^2)^-1 k^-2 exp(-klogk+2k)
G=s.series(s.exp(-sum(s.bernoulli(2*m)*invk**(2*m-1)/(m*(2*m-1)) for m in range(1,J+1))),invk,0,J+1).removeO()
AA=s.series(B**-2*G,invk,0,J+1).removeO()
alpha=[AA.coeff(invk,i) for i in range(J+1)]
print('alpha',alpha)
# non-Gaussian exponent, coefficient in z=1/sqrt(r)
L=[s.Integer(0)]+[(-1)**(h+1)*((h+1)*w+1)*v**(h+2)/((h+2)*(h+1)) for h in range(1,2*J+1)]
E=[s.Integer(1)]
for n in range(1,2*J+1):
 E.append(s.expand(sum(h*L[h]*E[n-h] for h in range(1,n+1))/n))
amp=[s.Integer(0)]*(2*J+1)
for l in range(J+1):
 for h in range(2*J-2*l+1):
  amp[2*l+h]+=alpha[l]*(-1)**h*s.binomial(l+h+1,h)*v**h

def gaussian_mean(p):
 ret=0
 for mon,c in s.Poly(s.expand(p),v).terms():
  power=mon[0]
  if power%2==0:ret+=c*s.factorial2(power-1)/(w+1)**(power//2)
 return s.factor(ret)
coeff=[]
for j in range(J+1):
 cc=gaussian_mean(sum(amp[h]*E[2*j-h] for h in range(2*j+1)))
 coeff.append(cc);print('c',j,cc)
with open('saddle_coefficients.txt','w') as f:
 f.write('alpha='+str(alpha)+'\n')
 for j,c in enumerate(coeff):f.write(f'c{j}(w)='+str(c)+'\n')
