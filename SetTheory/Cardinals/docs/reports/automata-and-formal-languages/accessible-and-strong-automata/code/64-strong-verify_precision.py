"""Regressions for exact complex phases and exponentially small large-k terms."""
import json
from pathlib import Path
import mpmath as mp
from generate_coefficients import generate,imaginary_unit_power
root=Path(__file__).parent
checks=[]
mp.mp.dps=100
for m in range(10005):
    expected=[mp.mpc(1),mp.j,mp.mpc(-1),-mp.j][m%4]
    assert imaginary_unit_power(m)==expected
checks.append({'exact_modulo4_phases':10005,'passed':True})
for k,J,lo,hi in [(2,5,70,100),(3,5,70,100),(4,5,70,100),(500,1,60,100)]:
    low=generate(k,J,lo);high=generate(k,J,hi,50)
    mp.mp.dps=hi+30
    max_relative=mp.mpf(0)
    for field in ['p','b','tau','alpha','small_boundary_source']:
        for a,b in zip(low[field],high[field]):
            aa,bb=mp.mpf(a),mp.mpf(b)
            if bb: max_relative=max(max_relative,abs((aa-bb)/bb))
            else: assert aa==0
    assert max_relative<mp.mpf(10)**(-lo+1)
    if k==500:
        assert mp.mpf(low['p'][1])<0 and mp.mpf(low['b'][1])<0
        mp.mp.dps=400
        rho=-mp.lambertw(-k*mp.exp(-k))/k;v=1-rho;c=1-k*rho
        expected=-k*rho*v/(2*c)
        err=abs((mp.mpf(high['b'][1])-expected)/expected)
        assert err<mp.mpf('1e-99')
        checks.append({'k':k,'order':J,'p1':low['p'][1],'b1':low['b'][1],
                       'working_digits':low['working_digits'],'closed_form_relative_error':mp.nstr(err,12)})
    checks.append({'k':k,'order':J,'digits_low':lo,'digits_high':hi,
                   'max_relative_difference':mp.nstr(max_relative,12),'passed':True})
    if k in [2,3,4]:
        (root/f'coefficients_k{k}.json').write_text(json.dumps(low,indent=2)+'\n')
(root/'precision_validation.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
