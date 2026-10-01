"""Exact elementary inequalities for a nontrivial analytic phase-curvature seed."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
T=F(14,5)
sin_lower=sum((-1)**j*T**(2*j+1)/F(factorial(2*j+1)) for j in range(8))
cos_upper=sum((-1)**j*T**(2*j)/F(factorial(2*j)) for j in range(7))
cos_lower=sum((-1)**j*T**(2*j)/F(factorial(2*j)) for j in range(8))
K_lower=sin_lower/T-2*cos_upper-2
F_lower=(2*T*T-1)*sin_lower+T*cos_lower
if not K_lower>F(1,250):raise RuntimeError('K(14/5)>1/250 failed')
if not F_lower>2:raise RuntimeError('F(14/5)>2 failed')
if not cos_upper<0:raise RuntimeError('Negative cosine seed failed')
record={'status':'PASS','T':str(T),'K_lower':str(K_lower),'K_target':'1/250','F_lower':str(F_lower),'F_target':'2','cos_upper':str(cos_upper),'method':'Alternating sine and cosine Taylor bounds, with rational arithmetic','scope':'Only the elementary base inequalities; the analytic curvature and density arguments are proved in the manuscript'}
Path(__file__).with_name('curvature_seed.json').write_text(json.dumps(record,indent=2)+'\n')
print('Exact regular-seed inequalities pass')
