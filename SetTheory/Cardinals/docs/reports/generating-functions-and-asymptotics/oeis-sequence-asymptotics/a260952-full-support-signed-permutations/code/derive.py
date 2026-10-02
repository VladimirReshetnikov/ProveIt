import sympy as s
from sympy.functions.combinatorial.numbers import stirling
from math import factorial
M=10
c=[0]*(M+1)
for n in range(1,M+1):c[n]=factorial(n)-sum(c[k]*factorial(n-k) for k in range(1,n))
x,q,d,lam=s.symbols('x q d lambda')
C=sum(c[k]*x**k for k in range(1,M+1))
beta=[s.expand((1-C)**2).coeff(x,k) for k in range(M+1)]
print('c',c);print('beta',beta)
p=[s.Integer(1)]+[-sum(c[k]*q**(-k)*stirling(m-1,k-1,kind=2) for k in range(1,m+1)) for m in range(1,M+1)]
print('OEIS A260952',[s.simplify(2**m*p[m].subs(q,2)) for m in range(M+1)])
S=(q+1)/q*(1-s.exp(-d))
logseries=s.series(-sum(beta[j]*(-1)**(j-1)*S**(j-2)/s.factorial(j-2) for j in range(2,7))/q,d,0,5).removeO().expand()
L2=-q/(q+1)**2;L1=(q+2)/(q+1)**2
print('late correction factorial basis h/m',s.factor(L1/L2))
for ell in range(5):
 z=s.factor(logseries.coeff(d,ell)/L2*(-1)**(ell+1)*s.factorial(ell))
 print('tau^%d/(m)_%d'%(ell+2,ell+2),z,'q2',z.subs(q,2))
# Inverse n expansion, with x=1/n. Factorial ratio (n)_j inverse
K=5
fall=lambda j:s.prod(1-r*x for r in range(j))
D=sum(beta[j]*x**j/fall(j) for j in range(K+1))
D=s.series(D,x,0,K+1).removeO()
L=s.series(1-sum(c[k]*q**(-k)*x**k/fall(k) for k in range(1,K+1)),x,0,K+1).removeO()
H=0
for j in range(K+1):
 # D(n-j) represented by replace x=1/(n-j)=x/(1-j*x)
 H+=q**j*s.factorial(j)*x**j/fall(j)*D.subs(x,x/(1-j*x))
H=s.series(H,x,0,K+1).removeO().expand()
print('D',D)
print('L',[s.factor(L.coeff(x,j)) for j in range(K+1)])
print('H',[s.factor(H.coeff(x,j)) for j in range(K+1)])
print('L1=H1',s.simplify(L.subs(q,1)-H.subs(q,1)))
# q=1+lambda/n. q^n=exp(lambda)*exp(sum ...)
Q=1+lam*x
E=s.exp(lam)*s.exp(sum((-1)**(r+1)*lam**r*x**(r-1)/r for r in range(2,K+2)))
# separately to avoid symbolic explosion
LC=s.series(L.subs(q,Q),x,0,K+1).removeO()
HC=s.series(H.subs(q,Q),x,0,K+1).removeO()
EC=s.series(E,x,0,K+1).removeO()
R=s.series(EC*LC-HC,x,0,K+1).removeO().expand()
print('SPARSE')
for j in range(K+1):print(j,s.factor(R.coeff(x,j)))
