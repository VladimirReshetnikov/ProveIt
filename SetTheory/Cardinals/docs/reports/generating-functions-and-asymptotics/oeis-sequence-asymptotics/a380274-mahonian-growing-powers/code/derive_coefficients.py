import sympy as s
z,u,j,n=s.symbols('z u j n')
K=5
sig=n*(n-1)*(2*n+5)/72
lam={m:s.series((s.bernoulli(2*m)/(2*m)*s.summation(j**(2*m)-1,(j,1,n))/sig**m).subs(n,1/z),z,0,K+1).removeO().expand() for m in range(2,K+2)}
T=sum((-1)**m*lam[m]*u**(2*m)/s.factorial(2*m) for m in lam)
# Series truncate termwise avoids symbolic explosion.
coeff=[s.expand(T).coeff(z,k) for k in range(K+1)]
E=[s.Integer(1)]
for k in range(1,K+1):
 E.append(s.expand(sum(i*coeff[i]*E[k-i] for i in range(1,k+1))/k))
def moment(poly,extra):
 p=s.Poly(poly,u)
 return sum(co*s.factorial2(pow[0]+extra-1) for pow,co in p.terms())
J={h:sum(moment(E[k],2*h)*z**k for k in range(K+1)) for h in range(4)}
a=s.series(J[1]/J[0],z,0,K+1)
b=s.series(J[2]/J[0]-3*(J[1]/J[0])**2,z,0,K+1)
c=s.series(-J[3]/J[0]+15*J[2]*J[1]/J[0]**2-30*(J[1]/J[0])**3,z,0,K+1)
print('variance=',sig)
for m in lam:print('lambda',2*m,':',lam[m])
print('a=',a);print('b=',b);print('c=',c)
print('J0=',J[0])
