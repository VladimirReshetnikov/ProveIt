"""Optional numerical witness discovery; NOT used by the exact checker."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
from bui_model import NAMES,load_profiles,horner,jacobian,matvec
ROOT=Path(__file__).resolve().parents[1]
t=Fraction(10000,43149)
P=load_profiles(ROOT/'data/profiles_18.csv')
a=[horner(p,t) for p in P]
J=jacobian(t,a)
M=np.array(J,dtype=float)
values,vectors=np.linalg.eig(M)
k=np.argmax(values.real)
v=vectors[:,k].real
if v.sum()<0:v=-v
v=v/v.max()
w=[int(round(x*10**12)) for x in v]
ratios=[x/Fraction(y) for x,y in zip(matvec(J,w),w)]
margin=min(ratios)-1
assert margin>Fraction(1,1000000)
obj={'evaluation_numerator':10000,'evaluation_denominator':43149,
     'prefix_size':18,'variable_order':NAMES,'positive_integer_vector':w,
     'certified_factor_numerator':1000001,'certified_factor_denominator':1000000,
     'discovery_eigenvalue_approx':float(values[k].real),
     'minimum_ratio_margin_approx':float(margin)}
(ROOT/'data/bui_spectral_certificate.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(obj,indent=2))
