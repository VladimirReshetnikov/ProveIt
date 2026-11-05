#!/usr/bin/env python3
"""Bounded exact check of the fixed-coordinate rank-repair obstruction."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
prior=here.parent/'p64-qcube72-free-main-obstruction/result.json'
raw=prior.read_bytes()
if hashlib.sha256(raw).hexdigest()!='65175e0ed6945fa2a09bd6c23d4e25df38301a1b831d93ab1fcabfbf0e535bee':raise RuntimeError('partial example drift')
x=json.loads(raw)
q,U,k,h,J,beta,K0,w,MC,MF=4,4096,10,4096,3,1,1,1,0,0
if any(x[name]!=value for name,value in [('q',q),('U',U),('k',k),('h',h)]) or q!=beta*J+1:
    raise RuntimeError('partial parameters drift')
if x['evaluated_graph_zero'] or x['first_gap']==0:raise RuntimeError('unexpected full-zero claim')
qm=q-1; lo,hi=2*q-1,q*q-q-1
all_bounds=[]; transport=[]
for F in range(1,q):
    for alpha in range(1,q):
        C=q-F-alpha
        if C<=0:continue
        G=qm*(q-F)+alpha
        if not lo<=G<=hi:raise RuntimeError('gap bound failed')
        R=G*(q*q-1)+J*(MC+q*MF)
        target=h+k-1-R
        if target%U==0:raise RuntimeError('unexpected inverse congruence')
        all_bounds.append({'F':F,'alpha':alpha,'G':G,'target':target})
        numerator=(K0+w)*C-F
        if numerator>0 and numerator%qm==0:
            z=numerator//qm
            if (K0+w)*C-F-z*qm!=0:raise RuntimeError('transport mismatch')
            transport.append({'F':F,'alpha':alpha,'z':z,'G':G,'target':target})
if not all_bounds or not transport or min(y['target'] for y in all_bounds)<=0 or max(y['target'] for y in all_bounds)>=U:
    raise RuntimeError('bounded rank-repair check failed')
result={'status':'PASS_PARTIAL_RANK_REPAIR_OBSTRUCTION','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'prior_result_sha256':hashlib.sha256(raw).hexdigest(),'gap_lower':lo,'gap_upper':hi,
        'pairs':all_bounds,'transport_pairs':transport,
        'scope':'Partial q=4 data only; fixed selected coordinates and ports, no full zero or compact44 nonexistence.'}
out=here/'result.json';payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
