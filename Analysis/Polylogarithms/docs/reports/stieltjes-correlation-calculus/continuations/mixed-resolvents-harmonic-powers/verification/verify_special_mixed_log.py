"""Independent Mellin/Hadamard quadrature for the q=r=0 mixed-log identity.
The eta coefficient is obtained from a subtracted positive-real Mellin
kernel; the left side uses direct local coordinate subtraction.
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=80
threshold=mp.mpf('1e-6')
cs=[mp.bernoulli(2*k)/mp.factorial(2*k) for k in range(1,9)]
def remainder(t):
    # h(t)+log(t)/t, h(t)=-log(1-exp(-t))/(exp(t)-1).
    if t<threshold:
        d=mp.mpf('.5')-sum(c*t**(2*k-1) for k,c in enumerate(cs,1))
        a=-mp.mpf('.5')+sum(c*t**(2*k-1)/(2*k) for k,c in enumerate(cs,1))
        phi=1-t/2+sum(c*t**(2*k) for k,c in enumerate(cs,1))
        return mp.log(t)*d-a*phi
    q=-mp.expm1(-t)
    return -mp.log(q)/mp.expm1(t)+mp.log(t)/t

def mellin_h(t):
    return -mp.log1p(-mp.exp(-t))/mp.expm1(t)

I0=mp.quad(remainder,[0,threshold,mp.mpf('.1'),1])+mp.quad(mellin_h,[1,2,5,mp.inf])
I1=mp.quad(lambda t:mp.log(t)*remainder(t),[0,threshold,mp.mpf('.1'),1])+mp.quad(lambda t:mp.log(t)*mellin_h(t),[1,2,5,mp.inf])
g=mp.euler
z2=mp.zeta(2)
z3=mp.zeta(3)
z2p=mp.diff(mp.zeta,2)
L=mp.log(2*mp.pi)
g3=(g**3-3*g*z2+2*z3)/6
eta=g3+I1

def delta(x):
    if x<threshold:
        return -sum(mp.zeta(2*k)*x**(2*k)/k for k in range(1,9))
    return mp.log(mp.sinpi(x)/(mp.pi*x))

def direct_integrand(x):
    if x==0 or x==1: return mp.mpf(0)
    logx=mp.log(x)
    d=delta(x)
    f=(logx+L+d)**2+mp.pi**2*(x-mp.mpf('.5'))**2
    return -mp.digamma(1+x)*f+(2*(logx+L)*d+d*d)/x+mp.pi**2*(x-1)

lhs=mp.quad(direct_integrand,[0,threshold,mp.mpf('.1'),mp.mpf('.5'),mp.mpf('.9'),1])
rhs=2*eta+2*z2p-(g**3+L**3)/3-g*z2-L*z2/2-2*z3/3
res=lhs-rhs
assert abs(I0)<mp.mpf('1e-72')
assert abs(res)<mp.mpf('1e-70')
record={'working_decimal_digits':mp.mp.dps,'eta':mp.nstr(eta,75),'mellin_constant_normalization_I0':mp.nstr(I0,15),'lhs_direct_coordinate_finite_part':mp.nstr(lhs,75),'rhs_independent_mellin_eta':mp.nstr(rhs,75),'absolute_residual':mp.nstr(abs(res),15),'methods':{'eta':'Mellin kernel subtracted at t=0; Bernoulli series stabilizes the difference.','lhs':'Direct fixed-coordinate Hadamard subtraction, with log-sinc series at x=0.'}}
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2))
print(json.dumps(record,indent=2))
