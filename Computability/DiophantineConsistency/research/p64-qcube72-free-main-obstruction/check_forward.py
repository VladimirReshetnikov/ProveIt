#!/usr/bin/env python3
"""Exact ring identity and bounded arithmetic checks of the forward sign route."""
import hashlib,json,runpy,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;root=here.parents[3]
verify=root/'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/verify.py'
if hashlib.sha256(verify.read_bytes()).hexdigest()!='97de6a4ff04997de2c5e0062c4c8b335cf4c8da6b1cd2b85b543948a62e3677b':raise RuntimeError('verifier drift')
Poly=runpy.run_path(str(verify))['Poly']
a,c,X=map(Poly.var,('a','c','X')); H=4*a+3; D=a*a+H
lhs=D*c*c+1-(X+a*c)**2
rhs=(2*a+2)*c*c+2*a*c*(c-X)+(c*c-X*X)+1
if lhs!=rhs: raise RuntimeError('root-gap polynomial identity failed')
count=divisible=0
for q in range(3,11):
    for w in range(1,6):
        for s in range(1,4):
            Y=q**3*s; X0=w*q; a0=Y*(X0+1); H0=4*a0+3; D0=a0*a0+H0
            c0=2*(a0+2); g0=2*(a0+2)**2-1; U=Y*Y
            if c0<2*(a0+2) or c0<=X0 or g0*g0!=1+D0*c0*c0 or g0<=X0+a0*c0:
                raise RuntimeError('forward sign sample failed')
            if (U*(g0-(X0+a0*c0)))%H0==0: divisible+=1
            count+=1
result={'status':'PASS_EXACT_IDENTITY_AND_FINITE_SAMPLES','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'exact_root_gap_identity':True,'natural_samples':count,'samples_with_integral_h':divisible,
        'scope':'Symbolic identity and bounded sign sanity checks, no model theorem or graph-zero proof.'}
out=here/'forward-result.json';payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check_forward.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
