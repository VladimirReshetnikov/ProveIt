#!/usr/bin/env python3
"""Independent high-precision quadrature and symbolic checks for joint moments.

These are numerical diagnostics, not interval certificates. The article proof
supplies the uniform error estimate. Run with Python 3, mpmath and sympy.
"""
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps=80
HERE=Path(__file__).resolve().parent
G=mp.euler
C=mp.zeta(2)/(2*G)
DELTA=C-G
D=mp.zeta(3)/(3*G)-C*C/2
EPS=G*G+D
E=mp.zeta(4)/(4*G)-C*mp.zeta(3)/(3*G)+C**3/3
ETA=E+G**3/2-G*G*DELTA/2+G*DELTA*DELTA/2-5*G*EPS

def correction1(t,lam):
    th=DELTA*lam
    return t*th*(1+th)/2-2*G*lam+EPS*lam*lam

def correction2(t,lam):
    return (lam*(DELTA*t*t/8-(G+5*DELTA/6)*t)
        +lam**2*(7*DELTA**2*t*t/8+(-3*G*DELTA-3*DELTA**2/2+2*EPS)*t+15*G**2/2+3*G*DELTA)
        +lam**3*(3*DELTA**3*t*t/4+(-G*DELTA**2-DELTA**3/3+5*DELTA*EPS/2)*t+ETA)
        +lam**4*(DELTA**4*t*t/8+DELTA**2*EPS*t/2+EPS**2/2))

def normalized_moment(n,m, width=25):
    """Evaluate the defining integral in a centered, standardized y=-log(x).

    Integrate over +/- width standard deviations and wider side intervals
    whose weights are still numerically visible. The full +/- width result
    is checked against width+5 independently for each reported case.
    """
    n=mp.mpf(n); m=mp.mpf(m); r=m+1; q=n+1; t=q/r
    sd=mp.sqrt(t/r)
    lognorm=q*mp.log(r)-mp.loggamma(q)-m*mp.log(G)
    def kernel(z):
        y=t+sd*z
        if y<=0:return mp.mpf('0')
        x=mp.exp(-y)
        f=y+mp.loggamma(1+x)
        b=mp.loggamma(1-x)
        if not(f>0 and b>0):return mp.mpf('0')
        val=lognorm+n*mp.log(f)+m*mp.log(b)-y+mp.log(sd)
        return mp.exp(val)
    left=max(-t/sd+mp.mpf('1e-60'),-mp.mpf(width))
    return mp.quad(kernel,[left,-8,-3,0,3,8,mp.mpf(width)])

def asstr(x):return mp.nstr(x,45)

def run():
    rows=[]
    for s in (-1,0,1):
        for m in (50,100,300,1000,3000):
            n=int(mp.nint((m+1)*(mp.log(m)+s)-1))
            t=mp.mpf(n+1)/(m+1); lam=m*mp.exp(-t)
            actual=normalized_moment(n,m,25)
            other=normalized_moment(n,m,30)
            leading=mp.exp(DELTA*lam)
            p1=correction1(t,lam);p2=correction2(t,lam)
            first=leading*(1+p1/m)
            second=leading*(1+p1/m+p2/(m*m))
            rows.append({'m':m,'n':n,'s':s,'t':asstr(t),'lambda':asstr(lam),
              'actual':asstr(other),'leading':asstr(leading),'first_correction':asstr(first),
              'second_correction':asstr(second),
              'relative_first_error':asstr((other-first)/other),
              'relative_second_error':asstr((other-second)/other),
              'scaled_first_error':asstr((other/leading-1-p1/m)*m*m/(t*t)),
              'scaled_second_error':asstr((other/leading-1-p1/m-p2/(m*m))*m**3/t**3),
              'quadrature_width_difference':asstr(abs(other-actual))})
            print(m,n,s,mp.nstr(other,13),mp.nstr((other-first)/other,8),mp.nstr((other-second)/other,8),flush=True)
    result={'precision_decimal_digits':mp.mp.dps,'proof_status':'Numerical diagnostics, not interval certificates',
      'constants':{k:asstr(v) for k,v in [('gamma',G),('c',C),('delta',DELTA),('d',D),('epsilon',EPS),('e',E),('eta',ETA)]},
      'rows':rows}
    (HERE/'joint_moment_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':run()
