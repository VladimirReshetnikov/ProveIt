"""Numerical discovery only; vector is frozen before independent validation."""
import json, time
from pathlib import Path
import mpmath as mp
from mixed_gaussian_common import numerical_euler_values as euler_values

out = Path(__file__).resolve().parents[1]/'data'
t0 = time.monotonic()
names, values = euler_values(14, 3600, 1100)
print('3600-term values at 1100 digits ready', time.monotonic()-t0, flush=True)
record = {'p':14, 'basket':names, 'Euler_terms':3600, 'value_digits':1100,
          'values':[mp.nstr(v,1060) for v in values], 'searches':[]}
(out/'s14_search.json').write_text(json.dumps(record,indent=2)+'\n')
mp.mp.dps = 850
vector = mp.pslq(mp.matrix(values), tol=mp.mpf('1e-800'),
                 maxcoeff=10**65, maxsteps=200000)
print('vector', vector, 'elapsed', time.monotonic()-t0, flush=True)
record['searches'].append({'digits':850, 'tolerance':'1e-800',
                          'maxcoeff':str(10**65), 'maxsteps':200000,
                          'vector':vector})
if vector:
    mp.mp.dps=1100
    record['retained_integer_residual']=mp.nstr(mp.fdot(values,vector),100)
    record['retained_normalized_residual']=mp.nstr(mp.fdot(values,vector)/vector[0],100)
    print('normalized residual',record['retained_normalized_residual'],flush=True)
record['elapsed_seconds']=time.monotonic()-t0
(out/'s14_search.json').write_text(json.dumps(record,indent=2)+'\n')
