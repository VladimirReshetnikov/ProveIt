#!/usr/bin/env python3
"""Exact arithmetic checks and high-precision (non-certified) diagnostics.

Run from any working directory. Writes only into the package's data folder.
"""
from __future__ import annotations
import csv, json, math, platform, time
from pathlib import Path
import mpmath as mp
from asymptotics import (saddle, profiles_from_s, log_volume, log_uniform,
                        exact_saddle_log, inverse_from_log, B)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'data'
OUT.mkdir(exist_ok=True)
mp.mp.dps = 55
started = time.time()
MS = [16,24,32,48,64,96]
requests = {}
for m in MS:
    req = []
    for a in [mp.mpf('0.25'),mp.mpf(1),mp.mpf(4)]:
        req.append(('quadratic_'+str(a), int(a*m*m)))
    for lam in [mp.mpf('0.5'),mp.mpf(1),mp.mpf(3)]:
        req.append(('centered_5_2_'+str(lam),
                    int(mp.nint(lam*mp.mpf(m)**mp.mpf('2.5')-mp.mpf(m*(m+1))/4))))
    req.append(('centered_9_4',
                int(mp.nint(mp.mpf('0.75')*mp.mpf(m)**mp.mpf('2.25')-mp.mpf(m*(m+1))/4))))
    if m <= 48:
        req.append(('cubic',m**3))
    requests[m] = req
NMAX = max(n for req in requests.values() for _,n in req)
arr=[1]+[0]*NMAX
samples=[]
small={}
# Published OEIS A238608 prefix used solely as a finite cross-check.
oeis=[1,1,5,75,2280,106852,6889527,569704489,57733506640,
      6944433285769,968356321790171,153738253618009045,
      27396489338187214000,5417302365503826145732,
      1177436831956414016252071,279074576444362385794783853,
      71649589941044468875380333533]
checks=1
assert oeis[0]==1
for m in range(1,max(MS)+1):
    for n in range(m,NMAX+1):
        arr[n] += arr[n-m]
    if m<=16:
        assert arr[m**3]==oeis[m]
        checks += 1
    if m in [2,3,5,8,12]:
        small[m]=arr[:401]
    for name,n in requests.get(m,[]):
        samples.append((m,n,name,arr[n]))
# Independent logarithmic-derivative/divisor recurrence.
for m,expected in small.items():
    sigma=[0]*401
    for d in range(1,m+1):
        for k in range(d,401,d):
            sigma[k]+=d
    p=[1]
    for n in range(1,401):
        num=sum(sigma[k]*p[n-k] for k in range(1,n+1))
        assert num % n == 0
        p.append(num//n)
        assert p[n] == expected[n]
        checks += 2

def st(x): return mp.nstr(x,22)
def writecsv(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

errors=[]; cross=[]; inverse=[]; exact=[]
coeff=json.loads((OUT/'coefficients.json').read_text())
def rational(text):
    p,q=(text.split('/')+['1'])[:2] if '/' in text else (text,'1')
    return mp.mpf(p)/mp.mpf(q)
d1=rational(coeff['D']['2']);d2=rational(coeff['D']['4'])
for m,n,name,count in samples:
    logp=mp.log(count)
    x=mp.mpf(n)+mp.mpf(m*(m+1))/4
    eps,d,e0,e1=profiles_from_s(saddle(mp.mpf(m*m)/x))
    lv=log_volume(m,x)
    err0=logp-(lv+m*d+e0)
    err1=err0-e1/m
    errors.append(dict(m=m,N=n,family=name,epsilon=st(eps),
                       log_error_E0=st(err0),log_error_E1=st(err1),
                       scaled_m2_error_E1=st(m*m*err1)))
    if 'centered' in name:
        r=2 if name=='centered_9_4' else 1
        actual=logp-lv-(m*d1*eps**2 if r==2 else 0)
        leading=(d2 if r==2 else d1)*m*eps**(2*r)
        cross.append(dict(m=m,N=n,family=name,r=r,
                          log_ratio=st(actual),leading_log_ratio=st(leading),
                          ratio=st(mp.exp(actual))))
    if name in ['quadratic_1.0','centered_5_2_1.0','cubic']:
        xi0=inverse_from_log(m,logp,False)
        xi1=inverse_from_log(m,logp,True)
        inverse.append(dict(m=m,N=n,family=name,
                            relative_error_leading=st(xi0/x-1),
                            relative_error_corrected=st(xi1/x-1),
                            scaled_m2_corrected=st(m*m*(xi1/x-1))))
    if name=='quadratic_1.0':
        ex0=exact_saddle_log(m,n,False)
        ex1=exact_saddle_log(m,n,True)
        exact.append(dict(m=m,N=n,log_error_gaussian=st(logp-ex0),
                          log_error_edgeworth1=st(logp-ex1)))
writecsv('uniform_errors.csv',errors)
writecsv('crossover_checks.csv',cross)
writecsv('inverse_checks.csv',inverse)
writecsv('finite_saddle_checks.csv',exact)
(OUT/'exact_samples.json').write_text(json.dumps([
    dict(m=m,N=n,family=name,p=str(count)) for m,n,name,count in samples],indent=2)+'\n')
# Profile derivative identity and small-epsilon coefficient diagnostics.
profile_checks=[]
for eps in map(mp.mpf,['0.001','0.1','0.8','2','3']):
    s=saddle(eps)
    _,d,e0,e1=profiles_from_s(s)
    assert abs(s/B(s)-eps)<mp.mpf('1e-45')
    assert d<0
    checks+=2
    profile_checks.append(dict(epsilon=st(eps),s=st(s),D=st(d),E0=st(e0),E1=st(e1)))
writecsv('profiles.csv',profile_checks)
summary=dict(status='PASS',exact_arithmetic_assertions=checks-10,
             numerical_profile_assertions=10,symbolic_assertions=coeff['exact_symbolic_assertions'],
             exact_samples=len(samples),max_m=max(MS),max_N=NMAX,
             digits=mp.mp.dps,python=platform.python_version(),mpmath=mp.__version__,
             elapsed_seconds=round(time.time()-started,3),
             qualifications=['Finite tests do not prove uniform error bounds.',
                             'mpmath diagnostics are not interval certificates.',
                             'No formal proof assistant was run.'])
(OUT/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
print('\nQuadratic N=m^2 log errors:')
for row in errors:
    if row['family']=='quadratic_1.0': print(row)
print('\nInverse diagnostics:')
for row in inverse:
    if row['family']=='quadratic_1.0': print(row)
