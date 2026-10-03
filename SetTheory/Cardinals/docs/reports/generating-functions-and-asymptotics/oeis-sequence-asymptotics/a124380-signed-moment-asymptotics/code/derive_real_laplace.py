import sympy as s
h,L,y=s.symbols('h L y')
# Expand integrand about x=√(n/2), t=x+y = 1/h+y. After factoring core exp[(2L−1)/h² +(L+1)/h+L/2]/sqrt(2π),
# phase E = Gaussian −2y² +(L+2)y plus h-polynomial perturbations.
ORDER=4
t=1/h+y
logt=L+s.log(1+h*y).series(h,0,ORDER+3).removeO()
logrho=(2/h**2+t+s.Rational(1,2))*logt-t*t+t-s.Rational(1,12)/t+s.Rational(1,360)/t**3-s.Rational(1,1260)/t**5
E=s.series(logrho-((2*L-1)/h**2+(L+1)/h+L/2),h,0,ORDER+1).removeO().expand()
print('E0',s.factor(E.coeff(h,0)))
P=[s.factor(E.coeff(h,j)) for j in range(1,ORDER+1)]
# Gaussian mean a=(L+2)/4, variance1/4
mu=(L+2)/4; var=s.Rational(1,4)
from functools import lru_cache
@lru_cache(None)
def mom(j):
 if j==0:return s.Integer(1)
 if j==1:return mu
 return s.expand(mu*mom(j-1)+(j-1)*var*mom(j-2))
def expect(p):
 return s.factor(sum(c*mom(pow[0]) for pow,c in s.Poly(s.expand(p),y).terms()))
R=s.Integer(0)
# recursion expΣh^jP_j
Q=[s.Integer(1)]
for j in range(1,ORDER+1):
 Q.append(s.expand(sum(l*P[l-1]*Q[j-l] for l in range(1,j+1))/j))
rels=[expect(q) for q in Q]
logs=[s.Integer(0)]
for j in range(1,ORDER+1):
 logs.append(s.factor(rels[j]-sum(l*logs[l]*rels[j-l] for l in range(1,j))/j))
print('relative coefficients')
for j,q in enumerate(rels):print(j,s.factor(q))
print('log coefficients')
for j,p in enumerate(logs):print(j,p)
