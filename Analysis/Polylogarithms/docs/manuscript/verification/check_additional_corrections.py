"""Independent defining-integral checks of late mathematical corrections."""
from pathlib import Path
import json
import mpmath as m
m.mp.dps=65
checks=[]
def check(name,left,right,tolerance='1e-48'):
    error=abs(left-right)
    checks.append(dict(name=name,residual=m.nstr(error,15),tolerance=tolerance,passed=bool(error<m.mpf(tolerance))))
    print(name,checks[-1]['passed'],m.nstr(error,8),flush=True)
pi=m.pi
a=m.mpf(1)/5
L5=lambda s:m.fsum(c*m.zeta(s,m.mpf(k)/5) for k,c in ((1,1),(2,-1),(3,-1),(4,1)))/5**s
rhs=m.mpf(2)/25+m.log(2*pi)/10+m.im(m.polylog(2,m.exp(2*pi*m.j/5)))/(4*pi)-m.mpf(6)/5*m.diff(m.zeta,-1)+m.diff(L5,-1)/20-m.mpf(29)/1200*m.log(5)
check('log-gamma fifth-point even-character correction',m.quad(m.loggamma,[0,a]),rhs)
def fp_integrand(t):
    if not t:return m.mpf(1)
    ker=m.mpf(1)/2+t/12-t**3/720+t**5/30240 if t<m.mpf('1e-12') else -1/m.expm1(-t)-1/t
    return ker*t/m.expm1(t/2)
check('elementary Herglotz derivative at one-half',m.quad(fp_integrand,[0,1,5,20,m.inf]),2+pi*pi/4)
check('convergent HPL endpoint with leading one',m.quad(lambda t:m.log(t)/(1-t) if t not in (0,1) else (0 if not t else -1),[0,1]),-m.zeta(2))
z=m.j/2
extra=m.im((m.log(abs(z))**2/3)*m.polylog(0,z))
check('modified-dilogarithm omitted Li0 term',extra,m.mpf(2)/15*m.log(2)**2)
roots=m.polyroots([1,0,1,-1],maxsteps=200)
z=next(t for t in roots if m.im(t)<0)
q=m.log(abs(z))
value=m.im(m.polylog(4,z)-q*m.polylog(3,z)+q*q*m.polylog(2,z)/3)
reference=m.mpf('-0.916010467826680838722383200166')
# The printed reference has only 30 decimal places; compare it at that scope.
check('corrected supergolden complex P4 display',value,reference,'1e-29')
result=dict(engine='mpmath '+m.__version__,decimal_digits=m.mp.dps,checks=checks,all_pass=all(c['passed'] for c in checks))
Path(__file__).with_name('additional-corrections-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
raise SystemExit(0 if result['all_pass'] else 1)
