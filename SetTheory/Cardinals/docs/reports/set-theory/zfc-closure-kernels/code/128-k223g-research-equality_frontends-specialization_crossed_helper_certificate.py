#!/usr/bin/env python3
"""Tiny exact closed certificates for T plus a crossed equality helper.

T(i,A): All_i A -> A.
C1(a,b,c): Eq(a,b) -> All_c Eq(b,a), with c != a,b.

No rho7, symmetry, equality vacuity, substitution, or GEN under assumptions
is accepted as a leaf. The classical TAUT leaves use the original retained
rho8/rho6 classical bridge. Uses only the bundled stdlib-only proof module.
"""
from pathlib import Path
from itertools import product
import hashlib,json
from combined_helper_certificate import (
    P,I,Q,Eq,assumptions,prop,export,read_export,prop_atoms,eval_prop,
)

def c1(a,b,c):
    if c in (a,b):raise ValueError('C1 gate')
    return P('C1',I(Eq(a,b),Q(c,Eq(b,a))),(a,b,c))
def spec(c,A):return P('T',I(Q(c,A),A),(c,A))
def roots_for(a,b,c):
    e,f=Eq(a,b),Eq(b,a)
    s=prop(I(e,f),c1(a,b,c),spec(c,f))
    h=prop(I(e,Q(c,e)),s,c1(b,a,c))
    return {'symmetry':s,'full_gated_equality_vacuity':h}

def check(t,seen,counts):
    if t in seen:return
    seen.add(t);counts[t.rule]=counts.get(t.rule,0)+1
    r,f=t.rule,t.form
    if r=='MP':
        p,q=t.args
        if p.form!=I(q.form,f):raise ValueError('Invalid MP')
        check(p,seen,counts);check(q,seen,counts)
    elif r=='TAUT':
        atoms=sorted(prop_atoms(f),key=repr)
        if any(not eval_prop(f,dict(zip(atoms,bits))) for bits in product((False,True),repeat=len(atoms))):
            raise ValueError('Nontautological TAUT leaf')
    elif r=='C1':
        a,b,c=t.args
        if c in (a,b) or f!=I(Eq(a,b),Q(c,Eq(b,a))):raise ValueError('Invalid C1')
    elif r=='T':
        c,A=t.args
        if f!=I(Q(c,A),A):raise ValueError('Invalid T')
    else:raise ValueError('Unpermitted rule '+r)

def main():
    roots={};groups={}
    for a,b,c in [('a','b','c'),(0,0,1),(0,1,2),(1,0,2),(1,1,0),(3,999,1001)]:
        for name,t in roots_for(a,b,c).items():
            if assumptions(t):raise ValueError('Open root')
            key=f'{name}_{a}_{b}_{c}';roots[key]=t
            seen=set();counts={};check(t,seen,counts)
            groups[key]={'nodes':len(seen),'rules':counts}
    data=export(roots)
    data['scope']='Exact closed C1+T proofs of symmetry and every full gated Eq-vacuity instance. Only TAUT, C1, T, MP leaves/nodes.'
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
    out=Path(__file__).with_name('specialization_crossed_helper_proofs.json');out.write_bytes(raw)
    seen=set();counts={}
    for name,t in read_export(json.loads(raw)).items():
        if t.form!=roots[name].form:raise ValueError('Reload mismatch')
        check(t,seen,counts)
    receipt={'status':'PASS','proof_sha256':hashlib.sha256(raw).hexdigest(),
             'proof_nodes':len(data['proof_nodes']),'formulas':len(data['formulas']),
             'roots':groups,'total_rules':counts,
             'scope':data['scope']+' TAUT uses the unchanged rho8/rho6 classical bridge; this does not certify a compiled TM table.'}
    Path(__file__).with_name('specialization_crossed_helper_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
