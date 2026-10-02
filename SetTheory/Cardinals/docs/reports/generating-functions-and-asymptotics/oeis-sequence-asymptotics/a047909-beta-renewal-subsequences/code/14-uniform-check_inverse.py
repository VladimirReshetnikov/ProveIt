"""Finite inverse identities and high precision diagnostics, not certification."""
from pathlib import Path
import json
import sympy as s
import mpmath as mp
r, h, d, d0, d1, L0, L1, c1, g, logm = s.symbols('r h d d0 d1 L0 L1 c1 g logm', nonzero=True)
# Expansion of the log carrier around k=m*r, through order m^-1.
residual = -g*d - logm/2 + L0 + h*(-d*d/(2*r)+L1*d+c1)
sub = s.series(residual.subs(d,d0+d1*h),h,0,2).removeO().expand()
d0formula = (L0-logm/2)/g
d1formula = (-d0formula*d0formula/(2*r)+L1*d0formula+c1)/g
assert s.simplify(sub.subs({d0:d0formula,d1:d1formula})) == 0
Lprime=s.diff(1-1/r+s.log(r)/2-s.log(r-1)-s.log(2*s.pi)/2,r)
assert s.simplify(Lprime-(1/r**2+1/(2*r)-1/(r-1)))==0
mp.mp.dps=70
rows=[]
for branch,ell in [('success','.2'),('success','1'),('success','2'),('failure','.2'),('failure','.8')]:
    ell=mp.mpf(ell); j=0 if branch=='success' else -1
    rho=mp.exp(1+mp.lambertw((ell-1)/mp.e,j))
    I=lambda z:1-z+z*mp.log(z)
    assert abs(I(rho)-ell)<mp.mpf('1e-65')
    assert (rho>1) if branch=='success' else (0<rho<1)
    c=lambda z:-(z**4+10*z**3-17*z**2+24*z-6)/(12*z**3*(z-1)**2)
    L=lambda z:1-1/z+mp.log(z)/2-mp.log(abs(z-1))-mp.log(2*mp.pi)/2
    Lp=lambda z:1/z**2+1/(2*z)-1/(z-1)
    for m in (1000,10000):
        gg=mp.log(rho); d0v=(L(rho)-mp.log(m)/2)/gg
        d1v=(-d0v*d0v/(2*rho)+Lp(rho)*d0v+c(rho))/gg
        kappa=m*rho+d0v+d1v/m
        # Explicit log carrier including c1/m (a legitimate smooth carrier).
        logtarget=lambda k:-m*I(k/m)-mp.log(m)/2+L(k/m)+c(k/m)/m+m*ell
        root=mp.findroot(logtarget,(kappa-mp.mpf('.01'),kappa+mp.mpf('.01')))
        err=abs(root-kappa)
        rows.append({'branch':branch,'ell':str(ell),'m':m,
                     'rho0':mp.nstr(rho,24),
                     'smooth_carrier_root':mp.nstr(root,24),
                     'kappa_error':mp.nstr(err,12),
                     'normalized_error':mp.nstr(err*m*m/(1+mp.log(m))**3,12)})
result={'symbolic_checks':'PASS: logarithmic corrections and L derivative',
        'branch_checks':'PASS: principal and lower real Lambert branches',
        'scope':'Finite smooth-carrier diagnostics only; no probability or integer-rounding certification',
        'numerics':rows}
Path(__file__).with_name('inverse.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
