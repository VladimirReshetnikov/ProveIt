#!/usr/bin/env python3
"""Independent univariate modular degree and leading-coefficient sanity check."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
path=here/'graph.json'; raw=path.read_bytes()
if hashlib.sha256(raw).hexdigest()!='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806': raise RuntimeError('graph drift')
graph=json.loads(raw); mod=1000003
coeff={n:i+1 for i,n in enumerate(graph['witnesses'])}
ports={'beta':3,'K0':5,'MC':7,'MF':11}
def trim(x):
    while len(x)>1 and x[-1]==0: x.pop()
    return x
def add(a,b,sign):
    out=[0]*max(len(a),len(b))
    for i,x in enumerate(a): out[i]=(out[i]+x)%mod
    for i,x in enumerate(b): out[i]=(out[i]+sign*x)%mod
    return trim(out)
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=(out[i+j]+x*y)%mod
    return trim(out)
values={n:[0,c] for n,c in coeff.items()}; values.update({n:[c] for n,c in ports.items()})
def get(v): return [v%mod] if isinstance(v,int) else values[v]
for name,op,a,b in graph['source']:
    x,y=get(a),get(b)
    values[name]=add(x,y,1) if op=='+' else add(x,y,-1) if op=='-' else mul(x,y)
out=values[graph['output']]
expected=(pow(ports['beta'],56,mod)*pow(coeff['J'],56,mod)*pow(coeff['T'],4,mod)*
          pow(coeff['f'],12,mod)*pow(coeff['s'],16,mod)*pow(coeff['w'],8,mod)*
          pow((coeff['eta']+coeff['zeta'])%mod,8,mod))%mod
if len(out)-1!=104 or out[-1]!=expected or expected==0: raise RuntimeError('degree or leading coefficient mismatch')
result={'status':'PASS_RAY_ONLY','graph_sha256':hashlib.sha256(raw).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'modulus':mod,'witness_ray_coefficients':coeff,'port_values':ports,
        'degree':len(out)-1,'leading_coefficient':out[-1],
        'scope':'One modular univariate ray; does not establish general upper degree or zero-equivalence.'}
outpath=here/'ray-check.json'; payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with outpath.open('x') as f: f.write(payload)
elif sys.argv[1:]: raise SystemExit('usage: python3 -I -S -B check_ray.py [--write]')
elif outpath.read_text()!=payload: raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
