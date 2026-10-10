"""Independent real-Mellin numerical audit; no rigorous quadrature claim."""
import json, time
from pathlib import Path
import mpmath as m

HERE=Path(__file__).resolve().parents[1]/'data'
r=json.loads((HERE/'s14_candidate.json').read_text())
m.mp.dps=110
t0=time.monotonic()
cuts=[m.mpf(0),m.mpf(1),m.mpf(4),m.mpf(16),m.inf]
S=-m.quad(lambda t:t**13*m.exp(-t)*m.log1p(m.exp(-2*t))/(1+m.exp(-2*t)),cuts)/m.factorial(13)
vals=[S]
print('S14 Mellin done',time.monotonic()-t0,flush=True)
for a in range(14,1,-2):
    b=15-a
    if b==1:
        g=-m.quad(lambda t:t**(a-2)*m.log1p(m.exp(-2*t))*m.atan(m.exp(-t)),cuts)/(2*m.factorial(a-2))
    else:
        g=m.quad(lambda t:t**(a-1)*m.im(m.j*m.exp(-t)*m.polylog(b,m.j*m.exp(-t))/(1-m.j*m.exp(-t))),cuts)/m.factorial(a-1)
    vals.append(g)
    print('g',a,b,'Mellin done',time.monotonic()-t0,flush=True)
beta=lambda s:(m.zeta(s,m.mpf(1)/4)-m.zeta(s,m.mpf(3)/4))/m.mpf(4)**s
vals += [m.pi**15]+[beta(2*j)*m.zeta(15-2*j) for j in range(1,7)]+[beta(14)*m.log(2)]
rr=m.fdot(vals,r['vector'])/r['vector'][0]
record={'status':'Independent Mellin diagnostics only','digits':m.mp.dps,
        'values':[m.nstr(x,105) for x in vals],
        'normalized_residual':m.nstr(rr,90),
        'seconds':time.monotonic()-t0}
(HERE/'s14_mellin_audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('Normalized residual',record['normalized_residual'],flush=True)
