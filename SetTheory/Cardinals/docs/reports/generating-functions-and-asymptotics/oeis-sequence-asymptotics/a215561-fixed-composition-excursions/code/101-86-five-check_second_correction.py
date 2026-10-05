"""Exact second correction from marked kernel Puiseux and Gaussian jets.

This uses no recurrence for the sequence. It records the complete finite
jets used by the two-dimensional Gaussian coefficient rule.
"""
from pathlib import Path
from math import factorial
import json,time
import sympy as s
start=time.time(); ROOT=Path(__file__).resolve().parent
e,X,Y=s.symbols('e X Y'); rt=s.sqrt(5)

def trunc(f,n):
    return s.series(f,e,0,n+1).removeO().expand()

a=e*X;b=e*Y;w=s.S.Zero
for j in range(1,7):
    c=s.symbols('w'+str(j)); wc=w+c*e**j
    F=trunc(2*s.sinh(wc)+4*s.exp(a)*s.sinh(b+2*wc),j).coeff(e,j)
    coeff=F.coeff(c)
    if coeff!=10:raise RuntimeError(('implicit slope',j,coeff))
    w=s.expand(w+(-F.subs(c,0)/10)*e**j)
    print('implicit order',j,flush=True)
P=trunc(2*s.cosh(w)+2*s.exp(a)*s.cosh(b+2*w),6)
phase=trunc(s.log(P)-a/2,6)
print('phase complete',time.time()-start,flush=True)

P4=trunc(P,4);pw2=trunc(2*s.cosh(w)+8*s.exp(a)*s.cosh(b+2*w),4)
c0=trunc(s.cosh(b+2*w)+s.exp(-a)*s.cosh(w)/2,4);dc=c0-s.Rational(3,2)
z=s.symbols('z');ac0=s.log((3+rt)/2)
ac=ac0
for j in range(1,5):
    ac+=s.diff(s.acosh(z),z,j).subs(z,s.Rational(3,2))*trunc(dc**j,4)/factorial(j)
ac=trunc(ac,4)
logamp=trunc(s.log(P4)-a-ac-s.log(pw2/P4)/2,4)
logampdiff=logamp-logamp.subs(e,0)
amp=trunc(s.exp(logampdiff),4)
print('amplitude complete',time.time()-start,flush=True)

# General e3/e1 from the coalescing logarithmic root and the other root.
v2=trunc(pw2/P4,2)
v3=trunc((2*s.sinh(w)+16*s.exp(a)*s.sinh(b+2*w))/P4,2)
v4=trunc((2*s.cosh(w)+32*s.exp(a)*s.cosh(b+2*w))/P4,2)
zeta=trunc(-s.exp(-ac-w-b),2)
zetaPz=trunc(zeta-1/zeta+2*s.exp(a)*(s.exp(b)*zeta*zeta-s.exp(-b)/zeta**2),2)
R3=trunc(s.Rational(3,2)+5*v3*v3/(36*v2**3)-v4/(12*v2*v2)-v3/(3*v2*v2)+1/(3*v2)+P4/zetaPz,2)
B1=trunc(s.Rational(3,8)-s.Rational(3,2)*R3,2)
print('transfer derivative complete',time.time()-start,flush=True)

# Equal-mark transfer to the next order, directly from exact roots.
x=s.symbols('x',positive=True);t=(1-x*x)/4
v=(-1+s.sqrt(9+4/t))/2;V=(-1-s.sqrt(9+4/t))/2
Ef=s.series(-(v-s.sqrt(v*v-4))*(V+s.sqrt(V*V-4))/(4*t),x,0,6).removeO().expand()
e1=s.simplify(Ef.coeff(x,1));e3=s.simplify(Ef.coeff(x,3));e5=s.simplify(Ef.coeff(x,5))
if s.simplify(B1.subs(e,0)-(s.Rational(3,8)-s.Rational(3,2)*e3/e1))!=0:raise RuntimeError('B1 identity')
B2=s.simplify(s.Rational(25,128)-s.Rational(45,16)*e3/e1+s.Rational(15,4)*e5/e1)

def moment(n,variance):
    if n%2:return s.S.Zero
    return s.factorial2(n-1)*variance**(n//2) if n else s.S.One
def gaussian(poly):
    return s.simplify(sum(c*moment(i,4)*moment(j,10) for (i,j),c in s.Poly(poly,X,Y).terms()))

# Angular Taylor series, with the Gaussian quadratic already removed.
angular=lambda f:s.expand(f.subs(e,s.I*e))
phasecorr=sum(s.I**j*phase.coeff(e,j)*e**(j-2) for j in range(3,7))
combined=trunc(angular(amp)*(1+e*e*angular(B1)+e**4*B2)*trunc(s.exp(phasecorr),4),4)
b1=gaussian(combined.coeff(e,2));b2=gaussian(combined.coeff(e,4))
c1=s.simplify(b1/4-s.Rational(7,80))
c2=s.simplify(b2/16-s.Rational(7,320)*b1+s.Rational(49,12800))
if s.simplify(c1-13*(rt-5)/50)!=0:raise RuntimeError(('c1',c1))
out={'passed':True,'implicit_jet':str(w),'phase_jets':{str(j):str(s.simplify(phase.coeff(e,j))) for j in range(2,7)},'normalized_amplitude_jets':{str(j):str(s.simplify(amp.coeff(e,j))) for j in range(1,5)},'transfer_B1_jets':{str(j):str(s.simplify(B1.coeff(e,j))) for j in range(3)},'puiseux_e5':str(e5),'transfer_B2':str(B2),'basketball_b1':str(b1),'basketball_b2':str(b2),'c1':str(c1),'c2':str(c2),'c2_numeric':str(s.N(c2,30)),'seconds':time.time()-start}
(ROOT/'second_correction.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
