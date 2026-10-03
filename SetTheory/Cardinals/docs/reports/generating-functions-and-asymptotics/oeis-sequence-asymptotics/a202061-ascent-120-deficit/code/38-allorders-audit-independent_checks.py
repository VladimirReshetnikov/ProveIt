#!/usr/bin/env python3
"""Independent finite algebra and quadrature checks; not a replacement for proof."""
import sympy as s
import mpmath as mp
x,A,g,B=s.symbols('x A g B')

def trunc(f,m): return s.series(f,x,0,m).removeO().expand()
p=[2*A-3,-2*A*A+10*A-s.Rational(33,2),s.Rational(8,3)*A**3-24*A*A+86*A-120]
# T=1/x, A=log T+c. Cancel the constant logs analytically.
kx=s.Rational(1,2)+A*x+sum(p[j-1]*x**(j+1) for j in range(1,4))
invk=trunc(x/kx,5)
S=trunc(sum(s.rf(s.Rational(3,2),j)*invk**j for j in range(5)),4)
res=trunc((kx-s.Rational(1,2))/x-A-s.log(2*kx)+s.log(S),4)
assert s.simplify(res)==0
print('PASS: original row equation verifies p1, p2, p3 exactly')
# Independent hand expansion from normalized J-/J+ through r^2.
r=s.symbols('r')
Jm=1+(1-g)*r+s.Rational(3,2)*(1-g)*r*r
Jp=1-g*r-s.Rational(3,2)*g*r*r
W=s.series(Jm**(-s.Rational(1,3))*(Jm+2*Jp)/3,r,0,3).removeO().expand()
a=s.Rational(3,2)*B+3*g
q=1+a*x+(s.Rational(7,2)*a-s.Rational(33,2)+3*g)*x*x
answer=trunc(q**s.Rational(2,3)*W.subs(r,3*x/q),3)
assert s.simplify(answer.coeff(x,1)-B)==0
assert s.simplify(answer.coeff(x,2)+B*B/4-s.Rational(7,2)*B+10)==0
print('PASS: P1=B, P2=-B^2/4+7B/2-10; all log(2) terms cancel')
mp.mp.dps=65
lg2=mp.log(2)
# Numerical direct convergent moments, independent of analytic continuation.
def logmoment(sign, rr, mm):
    # z=sin(t)^2, 0<t<pi/2. Endpoint cancellation is explicit numerically.
    def f(t):
        if not t: return mp.mpf('0')
        z=mp.sin(t)**2
        if z == 1: return mp.mpf('0')
        weight = mp.sqrt(z/(1-z)) if sign == -1 else mp.sqrt((1-z)/z)
        return weight*mp.log(z)**mm/(1-z)**rr*2*mp.sin(t)*mp.cos(t)
    return mp.quad(f,[mp.mpf('1e-35'),mp.pi/6,mp.pi/3,mp.pi/2-mp.mpf('1e-30')])
expected=[-2*mp.pi*(1-lg2),8*mp.pi*(1-lg2)/3,-2*mp.pi*lg2,8*mp.pi*lg2]
for args,want in zip([(-1,1,1),(-1,2,2),(1,1,1),(1,2,2)],expected):
    got=logmoment(*args)
    assert abs(got-want)<mp.mpf('1e-26'), (args,got,want)
print('PASS: all four beta-log moments by direct 65-digit quadrature')
# True truncated-potential action at a fixed core b=e^20, alpha=v=1,c=0.
def kval(t):
    a=mp.log(t)
    return t/2+a+(2*a-3)/t+(-2*a*a+10*a-mp.mpf('16.5'))/t**2+(mp.mpf(8)/3*a**3-24*a*a+86*a-120)/t**3
Y0=(2/(3*mp.pi**2))**(mp.mpf(1)/3)
kappa=mp.log(Y0)-2*mp.log(3)
print('Direct action residual: T, L, [A/(CF)-1-B/L-P2/L^2]*L^3/(1+|B|^3)')
for T in [100,200,400,800]:
    T=mp.mpf(T); k=kval(T); kp=mp.diff(kval,T)
    def f(t,sign):
        if abs(t)<mp.mpf('1e-18'):
            return 2/mp.sqrt(1-kp/k) if sign==-1 else 2*mp.sqrt(1-kp/k)*t*t
        w=t*t
        diff=mp.expm1(w)*kval(T-w)/k+(kval(T-w)-k)/k
        if not diff: return 2/mp.sqrt(1-kp/k) if sign==-1 else mp.mpf('0')
        return 2*t*mp.exp(-w)*diff**(mp.mpf(sign)/2)
    end=mp.sqrt(T-20)
    cuts=[mp.mpf(0)]+[mp.mpf(a) for a in [1,2,3,4,6,8,10,12,16,20] if a<end]+[end]
    im=mp.quad(lambda t:f(t,-1),cuts); ip=mp.quad(lambda t:f(t,1),cuts)
    L=mp.log(mp.sqrt(2)*im)+3*T/2-mp.log(k)/2
    logA=mp.log(mp.sqrt(2)*(im+2*ip))+(T+mp.log(k))/2
    ratio=mp.exp(logA-(L/3+mp.mpf(2)/3*mp.log(L)-mp.log(Y0)))
    b=kappa+mp.mpf(7)/3*mp.log(L)
    p2=-b*b/4+mp.mpf(7)/2*b-10
    residual=(ratio-1-b/L-p2/L**2)*L**3/(1+abs(b)**3)
    print(mp.nstr(T,8),mp.nstr(L,15),mp.nstr(residual,18))
    assert abs(residual)<1
print('PASS: exact fixed-core quadrature agrees with the independently checked P2 scale')
