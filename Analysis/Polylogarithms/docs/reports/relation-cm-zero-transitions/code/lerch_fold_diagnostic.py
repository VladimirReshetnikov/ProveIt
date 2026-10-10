"""Numerical diagnostic only: the proofs do not rely on this quadrature."""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=40
z2,z3,g=mp.zeta(2),mp.zeta(3),mp.euler

def kernel(t):
    y=mp.log(t)+g
    return y**3-3*z2*y+2*z3

def D(a,r,da=0,dr=0):
    def integr(t):
        e=mp.exp(-t)
        den=-mp.expm1(-t)+(1-r)*e
        return (-1)**da*t**(1+da)*mp.exp(-a*t)*kernel(t)*mp.factorial(dr)*e**dr/den**(1+dr)
    return mp.quad(integr,[0,mp.mpf('.001'),mp.mpf('.1'),1,mp.inf])

def run():
    a,u=mp.findroot(lambda a,u:(D(a,1-mp.power(10,-u)),D(a,1-mp.power(10,-u),da=1)),(mp.mpf('1.045'),mp.mpf('5.1')),tol=mp.mpf('1e-32'))
    r=1-mp.power(10,-u)
    out={'status':'numerical diagnostic, not an interval certificate', 'dps':mp.mp.dps,
         'a':str(a),'rho':str(r),'minus_log10_one_minus_rho':str(u),
         'D':str(D(a,r)),'D_a':str(D(a,r,da=1)),
         'D_aa':str(D(a,r,da=2)),'D_rho':str(D(a,r,dr=1))}
    out['square_root_coefficient']=str(mp.sqrt(-2*D(a,r,dr=1)/D(a,r,da=2)))
    path=Path(__file__).with_name('lerch_fold_diagnostic.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':run()
