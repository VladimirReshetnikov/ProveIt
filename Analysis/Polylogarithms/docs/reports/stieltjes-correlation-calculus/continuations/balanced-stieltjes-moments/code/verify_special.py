"""Independent special-value and primitive checks supplementing quadrature."""
from pathlib import Path
import json
import mpmath as mp
from balanced import Kernel

mp.mp.dps=55
checks=[]
def check(name,lhs,rhs):
    e=abs(lhs-rhs)/max(1,abs(rhs))
    checks.append({'name':name,'lhs':mp.nstr(lhs,55),'rhs':mp.nstr(rhs,55),
                   'scaled_residual':mp.nstr(e,12),'passed':bool(e<mp.mpf('1e-42'))})
    print(name,'PASS' if checks[-1]['passed'] else 'FAIL',mp.nstr(e,8),flush=True)

def order_derivative(m,z):
    # A 12th-order centered stencil avoids extremely small order perturbations
    # inside polylog's near-integer implementation. Two h values are checked.
    from math import comb
    def stencil(h):
        p=6
        return mp.fsum(mp.mpf((-1)**(k+1))*comb(2*p,p-k)/(k*comb(2*p,p))
            *(mp.polylog(m+k*h,z)-mp.polylog(m-k*h,z)) for k in range(1,p+1))/h
    with mp.workdps(85):
        d1=stencil(mp.mpf('1e-5'));d2=stencil(mp.mpf('1e-6'))
        if abs(d1-d2)>mp.mpf('1e-55'):
            raise ArithmeticError('Order-derivative step refinement failed')
        return +d2

def Pprime(m,a):
    plus=mp.mpf(-1) if a==mp.mpf('.5') else mp.exp(2j*mp.pi*a)
    minus=mp.conj(plus)
    return ((-1j)**m*(order_derivative(m,plus)-1j*mp.pi/2*mp.polylog(m,plus))
        +(1j)**m*(order_derivative(m,minus)+1j*mp.pi/2*mp.polylog(m,minus)))

for m,a in [(2,(1+1/mp.sqrt(3))/2),(2,(1-1/mp.sqrt(3))/2),(3,mp.mpf('.5'))]:
    check(f'polylog-root/m={m}/a={mp.nstr(a,8)}',(-1)**m*mp.factorial(m-1)/(2*mp.pi)**m*Pprime(m,a),
          (-1)**(m-1)*mp.diff(lambda s:mp.zeta(s,a),1-m))
check('zeta-second-derivative-at-zero',mp.diff(mp.zeta,0,2),
      mp.stieltjes(1)+mp.euler**2/2-mp.pi**2/24-mp.log(2*mp.pi)**2/2)
Z=lambda s:2*(2**s-2)*mp.zeta(s)-2**s
closed=mp.stieltjes(1)+mp.euler**2/2-mp.pi**2/24+mp.mpf('1.5')*mp.log(2)**2-mp.log(mp.pi)**2/2
check('half-filter-closed-first-Stieltjes',-mp.diff(Z,0,2)/2,closed)
Z3=lambda s:4*(2-2**s)*mp.zeta(s)+3*2**s-1
check('third-difference-closed-value',-mp.diff(Z3,-1),-6*mp.diff(mp.zeta,-1)-mp.mpf(5)/3*mp.log(2))
x=mp.mpf('.8');a=mp.mpf('1.4');b=mp.mpf('.6')
for q in range(3):
    A=-mp.diff(lambda z:x**z*(mp.zeta(z,x+a)-mp.zeta(z,x+b)),0,q+1)/(q+1)
    K=Kernel(q)
    check(f'anchored-primitive/q={q}',A,mp.quad(lambda t:K(x,t),[b,a]))
    check(f'shift-average/q={q}',mp.quad(lambda t:K(x,t),[0,.5,1]),mp.mpf(0))
report={'kind':'numerical diagnostics, NOT certified intervals','dps':55,
        'polylog_derivative_method':'12th-order central stencil, 85 digits, h=1e-5 and 1e-6',
        'count':len(checks),'passed':sum(c['passed'] for c in checks),
        'max_scaled_residual':mp.nstr(max(mp.mpf(c['scaled_residual']) for c in checks),12),
        'checks':checks}
out=Path(__file__).resolve().parents[1]/'results'/'special_checks.json'
out.write_text(json.dumps(report,indent=2)+'\n')
print(f"PASS COUNT {report['passed']} / {report['count']}")
if report['passed']!=report['count']:raise SystemExit(1)
