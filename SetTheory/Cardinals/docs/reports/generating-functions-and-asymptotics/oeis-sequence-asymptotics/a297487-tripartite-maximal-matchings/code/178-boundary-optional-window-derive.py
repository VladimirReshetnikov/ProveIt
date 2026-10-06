#!/usr/bin/env python3
"""Independent symbolic first correction for the moving-window saddle."""
import sympy as S
u,y=S.symbols('u y', positive=True)
s=1/u**2
chi=4/u+1/s
v=1/chi
b=-2*s/chi
A3=1/(6*s**2)+4/(3*u**2)
h1=s-s**4/6-(s**2+1/(2*s)+1/u)*y-y**2+A3*y**3
mu=[S.Integer(1),b]
for r in range(1,9): mu.append(S.factor(b*mu[r]+r*v*mu[r-1]))
def avg(poly):
 p=S.Poly(S.expand(poly),y)
 return S.factor(sum(c*mu[k[0]] for k,c in p.terms()))
c1=avg(h1)
m0=S.factor(v*avg(S.diff(h1,y)))
v1=S.factor(v**2*avg(S.diff(h1,y,2)))
print('h1 =',h1)
print('c1(u) =', c1)
print('mean constant =',m0)
print('variance N coefficient =',v1)
print('c1 numerator expanded =',S.expand(S.fraction(c1)[0]))
# second phase coefficient, independently derived from falling factorial and Stirling
h2=(-s**5/10-S.Rational(2,3)*s**3*y+s**2/2-s*y**2+y
    -S.Rational(1,12)*(1/s+1/u)+y**2/(4*s**2)+y**2/u**2
    -y**4/(12*s**3)-S.Rational(4,3)*y**4/u**3)
c2=avg(h2+h1**2/2)
ell2=S.factor(c2-c1**2/2)
print('h2 =',h2)
print('c2(u) =',c2)
print('ell2(u) =',ell2)
# u^3=2 at boundary, and u=2a; evaluate algebraically
for name,f in [('c1',c1),('mean constant',m0),('variance N coefficient',v1),('ell2',ell2)]:
 print('boundary',name, S.simplify(f.subs(u,2**S.Rational(1,3))))
# Direct formal phase expansion verifies h1,h2 without using their entered forms.
q=S.symbols('q')
x=s/q**2+y/q;z=u/q**2+2*y/q
M=2
L1=sum((-1)**(k+1)*(y*q/s)**k/S.Integer(k) for k in range(1,M+3))
L2=sum((-1)**(k+1)*(2*y*q/u)**k/S.Integer(k) for k in range(1,M+3))
G=3*y/q-x*L1-z*L2-(L1+L2)/2
for m in range(1,M+3):
 Sm=(S.bernoulli(m+1,x)-S.bernoulli(m+1,0))/(m+1)
 G-=2*q**(3*m)*Sm/m
G-=q**2*(1/s+1/u)/12
G=S.expand(G)
if S.simplify(G.coeff(q,1)-h1)!=0:raise RuntimeError('h1 differs')
if S.simplify(G.coeff(q,2)-h2)!=0:raise RuntimeError('h2 differs')
print('Formal generating expression independently reproduces h1 and h2.')
