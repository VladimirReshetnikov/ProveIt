"""Reproduce the version-specific complex-argument pitfall and test its repair."""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from vertical import G_hermite,kernel,bell_kernel

mp.mp.dps=60
z=mp.mpc('.8','.6')
records=[]
for n in range(3):
    lhs=G_hermite(n,z)
    rhs=mp.quad(lambda x:mp.exp(-z*x)*kernel(x)*bell_kernel(n,mp.log(x)),[0,mp.mpf('.25'),1,4,mp.inf])
    err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
    records.append({'name':f'complex-safe Hermite G_{n}','scaled_error':mp.nstr(err,8),
                    'passed':bool(err<mp.mpf('1e-35')),'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48)})
a=mp.mpf('1.3');n=2
lhs=G_hermite(n,a)
rhs=mp.stieltjes(n,a)+mp.log(a)**(n+1)/(n+1)
err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
records.append({'name':'positive-real control','scaled_error':mp.nstr(err,8),
                'passed':bool(err<mp.mpf('1e-35')),'lhs':mp.nstr(lhs,48),'rhs':mp.nstr(rhs,48)})
bad=mp.stieltjes(0,z);correct=-mp.digamma(z)
result={'status':'PASS' if all(r['passed'] for r in records) else 'FAIL',
        'precision_decimal_digits':60,'tests':len(records),'mpmath_version':mp.__version__,
        'interpretation':'Floating-point diagnostics, not interval certificates.',
        'records':records,'negative_control':{'function':'mp.stieltjes(0, 0.8+0.6i)',
        'returned':mp.nstr(bad,48),'expected_minus_digamma':mp.nstr(correct,48),
        'absolute_discrepancy':mp.nstr(abs(bad-correct),48),
        'limitation_reproduced':bool(abs(bad-correct)>mp.mpf('1e-3'))}}
path=Path(__file__).resolve().parents[1]/'results'/'complex_safe_replay.json'
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if result['status']!='PASS':raise SystemExit(1)
