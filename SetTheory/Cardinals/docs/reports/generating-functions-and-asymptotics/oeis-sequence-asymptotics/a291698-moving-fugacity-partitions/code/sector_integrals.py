"""Uncertified high-precision checks of the exact local sector integrals (12c)."""
import json
from pathlib import Path
import mpmath as mp
from checks import parameters,h_coefficients
mp.mp.dps=70
n=20000;alpha=1
u,A,N,t,s=parameters(n,alpha);L=mp.log(u);v=1/u
base=t*mp.besseli(1,2*s)*mp.exp(-2*s)
h=h_coefficients(u,9)
rows=[]
for j in range(4):
    Aj=A-2*mp.pi**2*j*j+2j*mp.pi*j*L
    center=2*mp.pi*j*t/L
    W=mp.pi*mp.sqrt(s)/L
    def integrand(w):
        z=t+1j*(center+w*t/mp.sqrt(s))
        logp=mp.mpf(0)
        for r in range(1,30):
            term=(-1)**(r+1)*v**r/(r*(-mp.expm1(-r*z)))
            logp+=term
            if abs(term)<mp.mpf('1e-80'):break
        logH=mp.log1p(v)/2-mp.polylog(2,-v)/z+v*z/(12*(1+v))-logp
        return mp.exp(logH+Aj/z+N*z-2*s)
    points=[-W]+[mp.mpf(k) for k in [-10,-5,0,5,10] if abs(k)<W]+[W]
    integral=(-1)**j*(t/mp.sqrt(s))*mp.quad(integrand,points)/(2*mp.pi*base)
    tj=mp.sqrt(Aj/N);sj=mp.sqrt(Aj*N)
    approx=(-1)**j*sum(h[m]*tj**(m+1)*mp.besseli(m+1,2*sj) for m in range(10))/(t*mp.besseli(1,2*s))
    rows.append({'j':j,'exact_local_sector_over_B0_real':mp.nstr(mp.re(integral),30),'exact_local_sector_over_B0_imag':mp.nstr(mp.im(integral),30),'absolute_error_M9_over_B0':mp.nstr(abs(approx-integral),12),'relative_complex_sector_error_M9':mp.nstr(abs(approx/integral-1),12)})
print(json.dumps(rows,indent=2))
Path(__file__).with_name('sector-integral-checks.json').write_text(json.dumps(rows,indent=2))
