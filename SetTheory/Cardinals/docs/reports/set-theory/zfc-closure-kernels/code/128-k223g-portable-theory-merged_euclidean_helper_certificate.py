#!/usr/bin/env python3
"""Exact closed proof interderivations for merged Euclidean/box helper G.

G(a,b,c) = Eq(c,a) -> (Eq(c,b) -> All_{RelCode(a,b)} Eq(a,b)).

The new theory derives literal old rho7 and H, not merely interpreted
equality formulas. Conversely rho7 and H derive G. Negative-conjunction
bundle transformations are checked as separate propositional roots.
All proof nodes are checked, exported, reloaded, and checked again.
"""
from pathlib import Path
from functools import cache
from itertools import product
import hashlib,json
from combined_helper_certificate import (
    P,I,Q,N,Ex,Eq,F,And,assumptions,mp,gen,taut,prop,
    rho1,rho2,rho6,mono,serial,export,read_export,prop_atoms,eval_prop,
)

def kappa(a,b):return 4*((a+b)*(a+b+1)//2+b)+1
@cache
def contra(t):
    a,b=t.form[1:]
    return prop(I(N(b),N(a)),t)
@cache
def emono(i,t):return contra(mono(i,contra(t)))
@cache
def merged(a,b,c):
    e=Eq(a,b)
    return P('G',I(Eq(c,a),I(Eq(c,b),Q(kappa(a,b),e))),(a,b,c))
@cache
def old_h(a,b):return P('OLD_H',I(Eq(a,b),Q(kappa(a,b),Eq(a,b))),(a,b))
@cache
def old_rho7(a,b,c):return P('OLD_RHO7',I(Eq(c,a),I(Eq(c,b),Eq(a,b))),(a,b,c))
@cache
def double_elim(i,A):
    return prop(I(Q(i,Q(i,A)),A),serial(i,Q(i,A)),rho6(i,A))
@cache
def reflexivity(x):
    e=Eq(x,x);z=kappa(x,x);d=Eq(z,x)
    d_to_qe=prop(I(d,Q(z,e)),merged(x,x,z))
    ex_qe=mp(emono(z,d_to_qe),rho1(z,x))
    return mp(rho6(z,e),ex_qe)
@cache
def ordinary_helper(a,b):
    return prop(I(Eq(a,b),Q(kappa(a,b),Eq(a,b))),merged(a,b,a),reflexivity(a))
@cache
def equality_box_elim(a,b):
    e=Eq(a,b);i=kappa(a,b)
    return prop(I(Q(i,e),e),mono(i,ordinary_helper(a,b)),double_elim(i,e))
@cache
def euclidean(a,b,c):
    return prop(I(Eq(c,a),I(Eq(c,b),Eq(a,b))),merged(a,b,c),equality_box_elim(a,b))
@cache
def symmetry(a,b):
    return prop(I(Eq(a,b),Eq(b,a)),euclidean(b,a,a),reflexivity(a))
@cache
def merged_from_old(a,b,c):
    return prop(merged(a,b,c).form,old_rho7(a,b,c),old_h(a,b))

def check(t,seen,counts):
    if t in seen:return
    seen.add(t);counts[t.rule]=counts.get(t.rule,0)+1
    r,f=t.rule,t.form
    if r=='MP':
        p,q=t.args
        if p.form!=I(q.form,f):raise ValueError('Invalid MP')
        check(p,seen,counts);check(q,seen,counts)
    elif r=='GEN':
        z,p=t.args
        if assumptions(p) or f!=Q(z,p.form):raise ValueError('Invalid or open GEN')
        check(p,seen,counts)
    elif r=='TAUT':
        atoms=sorted(prop_atoms(f),key=repr)
        if any(not eval_prop(f,dict(zip(atoms,bits))) for bits in product((False,True),repeat=len(atoms))):
            raise ValueError('Nontautological TAUT leaf')
    elif r=='rho1':
        z=f[1][1];atom=f[1][2][1]
        if atom[0]!='eq' or atom[1]!=z or f!=Ex(z,atom):raise ValueError('rho1')
    elif r=='rho2':
        z=f[1][1];a=f[1][2][1];b=f[1][2][2]
        if f!=I(Q(z,I(a,b)),I(Q(z,a),Q(z,b))):raise ValueError('rho2')
    elif r=='rho6':
        A=f[2];z=f[1][1][1]
        if f!=I(Ex(z,Q(z,A)),A):raise ValueError('rho6')
    elif r=='G':
        a,b,c=t.args;e=Eq(a,b)
        if f!=I(Eq(c,a),I(Eq(c,b),Q(kappa(a,b),e))):raise ValueError('G')
    elif r=='OLD_H':
        a,b=t.args;e=Eq(a,b)
        if f!=I(e,Q(kappa(a,b),e)):raise ValueError('OLD_H')
    elif r=='OLD_RHO7':
        a,b,c=t.args
        if f!=I(Eq(c,a),I(Eq(c,b),Eq(a,b))):raise ValueError('OLD_RHO7')
    else:raise ValueError('Unpermitted rule '+r)

def main():
    roots={};groups={}
    for a,b,c in [(0,0,0),(0,1,2),(1,0,0),(1,1,0),(3,999,1001)]:
        for name,t in [('reflexivity',reflexivity(a)),('ordinary_helper',ordinary_helper(a,b)),
                       ('equality_box_elim',equality_box_elim(a,b)),('original_rho7',euclidean(a,b,c)),
                       ('symmetry',symmetry(a,b)),('merged_from_old',merged_from_old(a,b,c))]:
            roots[f'{name}_{a}_{b}_{c}']=t
    # Exact baseline bundle: not(K -> (RV -> not(H))).
    K=('opaque','K');RV=('opaque','RV');H=('opaque','H')
    old_bundle=N(I(K,I(RV,N(H))))
    new_bundle=And(K,RV)
    roots['old_bundle_to_new_bundle']=taut(I(old_bundle,new_bundle))
    roots['old_bundle_projects_helper']=taut(I(old_bundle,H))
    roots['new_bundle_and_helper_to_old_bundle']=taut(I(new_bundle,I(H,old_bundle)))
    for name,t in roots.items():
        if assumptions(t):raise ValueError('Open root')
        seen=set();counts={};check(t,seen,counts)
        if name.startswith(('reflexivity','ordinary_helper','equality_box_elim','original_rho7','symmetry')):
            if 'OLD_H' in counts or 'OLD_RHO7' in counts:raise ValueError('Circular old-theory premise')
        if name.startswith('merged_from_old') and 'G' in counts:raise ValueError('Circular G premise')
        groups[name]={'nodes':len(seen),'rules':counts}
    data=export(roots)
    data['scope']='Closed exact native-formula interderivations. G+rho1/2/6+classical TAUT derives H and old rho7; oldH+oldrho7 derivesG. Exact negative-bundle transformations included. No changed-TM theorem asserted.'
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
    out=Path(__file__).with_name('merged_euclidean_helper_proofs.json');out.write_bytes(raw)
    seen=set();counts={}
    for name,t in read_export(json.loads(raw)).items():
        if t.form!=roots[name].form:raise ValueError('Reloaded root mismatch')
        check(t,seen,counts)
    receipt={'status':'PASS','proof_sha256':hashlib.sha256(raw).hexdigest(),
             'proof_nodes':len(data['proof_nodes']),'formulas':len(data['formulas']),
             'roots':groups,'total_rules':counts,
             'scope':data['scope']+' TAUT abbreviates the unchanged rho8/rho6 classical bridge.'}
    Path(__file__).with_name('merged_euclidean_helper_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='roots'},indent=2))
if __name__=='__main__':main()
