import sympy as s
from math import comb
P=s.pi; I=s.I; L=s.Symbol('L',real=True); G=s.Symbol('G',real=True)
def beta(n):
 return (-1)**((n-1)//2)*s.euler(n-1)*P**n/(2**(n+1)*s.factorial(n-1)) if n%2 else (G if n==2 else s.Symbol('beta'+str(n),real=True))
def li(n,c):
 c%=4
 if c==0:return s.zeta(n)
 if c==2:return -L if n==1 else -(1-s.Rational(2)**(1-n))*s.zeta(n)
 x=-L/2 if n==1 else -s.Rational(2)**(-n)*(1-s.Rational(2)**(1-n))*s.zeta(n)
 return x+(-1 if c==3 else 1)*I*beta(n)
def B(j,c):
 if c%4==0:return 2*s.zeta(j) if j%2==0 else s.S.Zero
 return s.expand(li(j,c)+(-1)**j*li(j,-c))
def parity(p,q,c,d):
 w=p+q;r=(c+d)%4
 v=sum((-1)**j*comb(w-j-1,p-1)*B(j,r)*li(w-j,c) for j in range(1,q+1))
 v+=sum(comb(w-j-1,q-1)*B(j,r)*li(w-j,-d) for j in range(1,p+1))
 v-=comb(w-1,p)*li(w,-d)+comb(w-1,q)*li(w,c)+B(p,c)*li(q,-d)
 v=(-1)**q*v+(-1)**w*li(w,-r)
 return s.simplify(s.expand(v)/(2 if w%2 else 2*I))
for w in range(2,7):
 for c,d in [(1,1),(2,1),(1,2)]:
  for p in range(1,w):
   q=w-p
   v=parity(p,q,c,d)
   print('value',p,q,c,d,'=',v)
  if w>=3:
   print('diff',w, c,d,'=',s.simplify(parity(1,w-1,c,d)-parity(w-1,1,d,c)))
