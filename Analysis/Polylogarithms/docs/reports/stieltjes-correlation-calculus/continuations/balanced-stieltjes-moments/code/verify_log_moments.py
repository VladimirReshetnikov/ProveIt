"""Ordinary logarithmic moments at Bernoulli roots: independent diagnostics."""
from pathlib import Path
import json
import mpmath as mp
from balanced import Term,elementary,mellin_integral
mp.mp.dps=55
checks=[]
def check(name,lhs,rhs):
    error=abs(lhs-rhs)/max(1,abs(rhs))
    checks.append({'name':name,'lhs':mp.nstr(lhs,55),'rhs':mp.nstr(rhs,55),
                   'scaled_residual':mp.nstr(error,12),'passed':bool(error<mp.mpf('1e-42'))})
    print(name,'PASS' if checks[-1]['passed'] else 'FAIL',mp.nstr(error,8),flush=True)
def Q(u,q):
    c=[mp.mpf(1)]
    H=[mp.mpf(0),mp.digamma(u)+mp.euler]+[mp.zeta(r)-mp.zeta(r,u) for r in range(2,q+1)]
    for n in range(1,q+1):
        c.append(mp.fsum((-1)**(r-1)*H[r]*c[n-r] for r in range(1,n+1))/n)
    return mp.factorial(q)*c[q]
def alpha(m):
    e=elementary(m)
    return mp.factorial(m-1)*mp.fsum((-1)**(m-j)*e[j]*mp.zeta(m-j) for j in range(m-1))-mp.harmonic(m-1)
for m in range(1,7):
    check(f'alpha/m={m}',mp.diff(lambda u:Q(u,m-1),m),alpha(m))
for m,a in [(1,mp.mpf('.5')),(2,(1+1/mp.sqrt(3))/2),(3,mp.mpf('.5'))]:
    v=mellin_integral(m,[Term(1,m-1,a,1)])
    target=(-1)**(m-1)*(alpha(m)*mp.diff(lambda s:mp.zeta(s,a),1-m)
                         -mp.diff(lambda s:mp.zeta(s,a),1-m,2)/2)
    check(f'logarithmic-root/m={m}',v,target)
    if m==1:
        check('closed-logarithmic-digamma',v,mp.log(2)**2/4+mp.log(2)*mp.log(2*mp.pi)/2)
    if m==3:
        rhs=3/(16*mp.pi**2)*(mp.diff(mp.zeta,3)+mp.zeta(3)*(3*mp.zeta(2)-2*mp.zeta(3)-mp.euler-mp.log(2*mp.pi)+mp.log(2)/3))
        check('closed-logarithmic-third-zeta',v,rhs)
report={'kind':'numerical diagnostics, NOT certified intervals','dps':55,
        'count':len(checks),'passed':sum(c['passed'] for c in checks),
        'max_scaled_residual':mp.nstr(max(mp.mpf(c['scaled_residual']) for c in checks),12),
        'checks':checks}
(Path(__file__).resolve().parents[1]/'results'/'log_moment_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(f"PASS COUNT {report['passed']} / {report['count']}")
if report['passed']!=report['count']:raise SystemExit(1)
