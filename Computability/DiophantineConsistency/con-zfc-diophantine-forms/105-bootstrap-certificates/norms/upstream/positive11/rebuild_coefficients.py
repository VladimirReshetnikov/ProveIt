#!/usr/bin/env python3
"""Rebuild all four compact44 coefficients and compare every integer byte."""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('compact44',ROOT/'native_recipe/build_coefficients.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
data=m.recipe();geometry=m.finite_audit(data);controller=m.padding_certificate(data)
B=1<<m.D_BITS
DC=sum(c<<(m.B_BITS*e) for e,c in data['dc'].items())
DR=1<<(m.B_BITS*m.SHIFT)
MF=4+sum(data['mu']<<(m.B_BITS*T) for T in (m.T1,m.T2))
MF+=sum(1<<(m.B_BITS*t) for t,*_ in data['targets'])
MF+=sum(c<<(m.B_BITS*e) for e,c in data['padding'].items())
MC=B-1-sum(1<<(m.B_BITS*e) for e in data['E'] if e!=1)-2*(1<<(m.B_BITS*1063))
values={'beta':B-1,'K':DC+B*DR,'MC':MC,'MF_source':MF+B-1}
checks={}
for name,v in values.items():
    raw=v.to_bytes((v.bit_length()+7)//8,'little')
    actual=gzip.decompress((ROOT/'coefficients'/(name+'.bin.gz')).read_bytes())
    if raw!=actual:raise ValueError('coefficient mismatch: '+name)
    checks[name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
out={'status':'PASS','geometry':geometry,'controller':controller,'ports':checks,'scope':'finite coefficient reconstruction from the literal transition list'}
(ROOT/'COEFFICIENT_REBUILD.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','ports':len(checks),'raw_bytes':sum(x['bytes'] for x in checks.values())}))
