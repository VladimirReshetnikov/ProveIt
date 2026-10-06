"""Independent direct expansion for P1, P2, and c1; writes only stdout."""
import sympy as S
s,L,a,U,V=S.symbols('s L a U V',positive=True,real=True)
i=S.I
# Expanding at exp(L)=2; m=L+M, h=x-y over 2
r=L-a*s**2
def trunc(p,lo=0,hi=7):
 return S.expand(p).series(s,0,hi).removeO().expand()
m=trunc(r*sum((i*U*s**3)**j/S.factorial(j) for j in range(4))*sum((-1)**j*(V*s**2)**(2*j)/S.factorial(2*j) for j in range(3)),hi=7)
h=trunc(i*r*sum((i*U*s**3)**j/S.factorial(j) for j in range(4))*sum((-1)**j*(V*s**2)**(2*j+1)/S.factorial(2*j+1) for j in range(3)),hi=7)
M=trunc(m-L,hi=7)
eM=trunc(sum(M**j/S.factorial(j) for j in range(4)),hi=7)
e2M=trunc(sum((2*M)**j/S.factorial(j) for j in range(4)),hi=7)
ch=trunc(1+h*h/2,hi=7)
d=trunc(4*(eM*ch-e2M),hi=7)
print('d=',d)
# reciprocal given leading 4*a*s^2
w=trunc(d/(4*a*s**2)-1,hi=5)
inv=trunc((1-w+w*w-w**3+w**4)/(4*a*s**2),hi=3)
g=trunc(2*m+inv-1,hi=3)
phase=trunc(g+2/s**4*sum((a/L*s*s)**j/S.Integer(j) for j in range(1,5))-2*i*U/s,hi=3)
# replace a**2=L/8 via simplify with direct substitution
phase=S.simplify(phase.subs(a,S.sqrt(L/8)))
for k in [-2,-1,0,1,2]:
 print('P',k,'=',S.simplify(S.expand(phase).coeff(s,k)))
P0=S.expand(phase).coeff(s,0)
P1=S.expand(phase).coeff(s,1)
P2=S.expand(phase).coeff(s,2)
# gaussian P0=C0-A*U**2-B*V**2
A=-S.expand(P0).coeff(U,2); B=-S.expand(P0).coeff(V,2)
def moment(poly):
 res=0
 for (p,q),c in S.Poly(S.expand(poly),U,V).terms():
  if p%2 or q%2: continue
  res += c*S.factorial2(p-1)*S.factorial2(q-1)/(2*A)**(p//2)/(2*B)**(q//2)
 return S.simplify(res)
print('A=',A,'B=',B)
C0=phase.expand().coeff(s,0).subs({U:0,V:0})
print('C0=',S.simplify(C0))
print('c1=',S.factor(moment(P2+P1**2/2)))
print('c1numeric=',S.N(moment(P2+P1**2/2).subs(L,S.log(2)),40))
