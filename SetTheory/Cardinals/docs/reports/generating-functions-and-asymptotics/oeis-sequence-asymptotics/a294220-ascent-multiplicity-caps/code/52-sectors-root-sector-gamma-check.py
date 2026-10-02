import sympy as S
h,s=S.symbols('h s');N=3
sig=[1/(1-s)]
for k in range(N):sig.append(S.factor(-s*S.diff(sig[-1],s)/(1-s)))
for r in [1,2,3]:
 s0=S.Rational(r,r+1)
 amp=S.series((s-S.harmonic(r)*h)*sum(sig[j]*h**j for j in range(N+1))**r,h,0,N+1).removeO().expand()
 av=0
 moments={}
 for j in range(2*N+1):
  moments[j]=S.expand(sum(S.binomial(j,k)*(-s0)**(j-k)*S.prod(r+i*h for i in range(1,k+1))/(r+1)**k for k in range(j+1)))
 for a in range(N+1):
  f=amp.coeff(h,a)
  for j in range(2*(N-a)+1):
   av+=h**a*S.diff(f,s,j).subs(s,s0)/S.factorial(j)*moments[j]
 av=S.series(av/(s0*(1-s0)**(-r)),h,0,N+1).removeO()
 st=S.exp(sum(S.bernoulli(2*k)*(S.Rational(r)**(1-2*k)-r)*h**(2*k-1)/(2*k*(2*k-1)) for k in range(1,3)))
 mser=S.series(av*st,h,0,N+1).removeO()
 bser=S.series((1+h)**S.Rational(3-r,2)*mser.subs(h,h/(1+h)),h,0,N+1)
 print(r,bser)
