#!/usr/bin/env python3
"""Exact polynomial checks and exploratory high-precision optimal-filter candidates.
No floating-point check here is used as proof of a global optimum.
Requires Python 3 and mpmath. Run: python reproduce.py > computations.txt
"""
from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 55

def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def power(a,k):
    p=[F(1)]
    for _ in range(k): p=mul(p,a)
    return p

def fmt(x,n=17): return mp.nstr(x,n)
print('Exact polynomial identities (ascending coefficients)')
# beta=0, theta with cos(theta) = -1/3, nonconsecutive triple.
p=mul([F(1),F(1)],[F(1),F(-2,3),F(1)])
assert p==[F(1),F(1,3),F(1,3),F(1)]
assert all(x>0 for x in p)
print('wide paired triple, cos(theta)=-1/3:', [str(x/sum(p)) for x in p])
p=mul([F(1),F(1)],[F(1),F(-1),F(1)])
assert p==[F(1),F(0),F(0),F(1)]
print('boundary ratio 5:', [str(x/sum(p)) for x in p])
p=power([F(1),F(1),F(1)],3)
assert p==[F(1),F(3),F(6),F(7),F(6),F(3),F(1)]
print('two frequencies at ratio 2, equal jet order 3:', [str(x/sum(p)) for x in p])

def candidate(lams, guess):
    def equations(t,T,w):
        return tuple(w*mp.cos(l*t)+(1-w)*mp.cos(l*T) for l in lams)
    t,T,w=mp.findroot(equations,guess,tol=mp.mpf('1e-50'))
    assert 0<t<T and 0<w<1
    # Dual direction: orthogonal to the inner value and derivative.
    a=[mp.cos(l*t) for l in lams]; b=[-l*mp.sin(l*t) for l in lams]
    c=[a[(i+1)%3]*b[(i+2)%3]-a[(i+2)%3]*b[(i+1)%3] for i in range(3)]
    c=[x/mp.sqrt(sum(y*y for y in c)) for x in c]
    if sum(c)<0: c=[-x for x in c]
    def g(x): return sum(cj*mp.cos(l*x) for cj,l in zip(c,lams))
    gp=lambda x: -sum(cj*l*mp.sin(l*x) for cj,l in zip(c,lams))
    gpp=lambda x: -sum(cj*l*l*mp.cos(l*x) for cj,l in zip(c,lams))
    print('frequencies:', ', '.join(map(fmt,lams)))
    print('centered t,T, inner total mass:', ', '.join(map(fmt,[t,T,w])))
    print('diameter:', fmt(2*T),'ratio exp(width):',fmt(mp.exp(2*T)))
    print('dual coefficients:', ', '.join(map(fmt,c)))
    print('g(t),g(T),g\'(t):', ', '.join(map(fmt,[g(t),g(T),gp(t)])))
    print('g\'\'(t),-g\'(T),g(0):',', '.join(map(fmt,[gpp(t),-gp(T),g(0)])))
    print('minimum on 2001 equally spaced test points:',fmt(min(g(T*i/2000) for i in range(2001))))
    print('moment residual max:',fmt(max(map(abs,equations(t,T,w)))))
    print('Uncertified numerical evidence only.\n')
    return t,T,w

print('\nPerturbation away from harmonic block:')
candidate(tuple(map(mp.mpf,['1','2.01','3.03'])),(mp.pi/4,3*mp.pi/4,mp.mpf('.5')))
print('Exact local slice (1,b,3), b=2.01:')
b=mp.mpf('2.01'); t,T,w=candidate((mp.mpf(1),b,mp.mpf(3)),(mp.pi/4,3*mp.pi/4,mp.mpf('.5')))
assert abs(2*T-(mp.pi+mp.pi/b))<mp.mpf('1e-45')
print('First three zeta ordinates (numerically computed; not certified):')
ls=tuple(mp.im(mp.zetazero(k)) for k in (1,2,3))
h=2*mp.pi/(ls[0]+ls[2]); theta=mp.pi-ls[0]*h
w=(1+2*mp.cos(theta))/(2+2*mp.cos(theta)) # inner mass = (1+2c)/(2+2c)? correction below
# P=1+(1+2c)z+(1+2c)z^2+z^3, inner total = (1+2c)/(2+2c).
candidate(ls,(h/2,3*h/2,w))
print('Exact two-ordinate equal-jet theorem, illustrative m=1,2,3:')
for m in (1,2,3):
    L=4*mp.pi*m/(ls[0]+ls[1])
    print('m=',m,' width=',fmt(L),' ratio=',fmt(mp.exp(L)))
