"""High-precision regressions; numerical quadrature is not interval certification."""
import json
from pathlib import Path
import mpmath as m
m.mp.dps=60
rho=m.log(4)
rows=[]

def require(condition,message):
    if not condition:
        raise RuntimeError(message)

def pair(value):
    return {'real':m.nstr(m.re(value),35),'imag':m.nstr(m.im(value),35)}

for k in (0,1,2):
    z=rho+2*m.pi*1j*k
    g=1+k%2
    kap=(g*g*m.pi*m.pi/(4*z))**(m.mpf(1)/3)
    c1=kap**2*(1-z)/2-5/(36*kap)
    c2=kap**4*(1-z)**2/8+kap*(53*z-17)/72-35/(2592*kap**2)
    T0=z/2-3
    for n in (512,4096):
        nn=m.mpf(n); lam=nn**(m.mpf(1)/3)
        r=abs(z*kap)*nn**(-m.mpf(2)/3)
        alpha_s=2*m.arg(z)/3
        def circ(alpha):
            delta=r*m.exp(1j*alpha); u=delta/z
            w=m.sqrt(m.expm1(delta))
            T=(z-delta)/2+g*m.pi/w-3*m.atan(w)/w
            return u*m.exp(T-T0-3*kap*lam-(n+1)*m.log(1-u))
        pts=sorted(set([-m.pi,m.pi,alpha_s]+[
            max(-m.pi,min(m.pi,alpha_s+i/m.sqrt(lam))) for i in range(-6,7)]))
        ratio=m.sqrt(3*m.pi/kap)*nn**(m.mpf(5)/6)/(2*m.pi)*m.quad(circ,pts)
        def bank(x):
            q=m.sqrt(-m.expm1(-x))
            B=2*m.exp(x/2-3*m.atanh(q)/q)
            return (-1)**k*B*m.sin(g*m.pi/q)/m.pi*m.exp(-(n+1)*m.log(1+x/z))
        X=m.mpf(16)
        pts=sorted(set([r,X]+[a for a in [2*r,4*r,8*r,m.mpf(1),m.mpf(2),m.mpf(4),m.mpf(8)] if r<a<X]))
        integ=m.quad(bank,pts)
        normalization=m.exp(-T0-3*kap*lam)*m.sqrt(3*m.pi/kap)*nn**(m.mpf(5)/6)
        ratio+=integ/z*normalization
        # B(x)<=2 exp(-x), so this is a rigorous bound for the omitted lips.
        tail=2*m.exp(-X)/m.pi*abs(z+X)**(-n-1)*abs(z)**n*abs(normalization)
        require(tail<m.mpf('1e-70'),'Analytic bank-tail bound too large')
        scaled=(ratio-(1+c1/lam+c2/lam**2))*lam**3
        require(abs(scaled)<100,'Regression residual exceeded expected finite test envelope')
        if k==0:
            require(abs(m.im(ratio))<m.mpf('1e-45'),'Conjugation regression failed')
        rows.append({'k':k,'n':n,'normalized_sector':pair(ratio),
                     'n_scaled_remainder_after_c2':pair(scaled),
                     'omitted_bank_tail_bound':m.nstr(tail,12)})
result={'status':'pass','mpmath_version':m.__version__,'decimal_precision':m.mp.dps,
        'scope':'Numerical quadrature regressions, not interval certificates',
        'rows':rows}
Path('checks').mkdir(exist_ok=True)
Path('checks/numerical_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
