#!/usr/bin/env python3
"""Fully expanded template metrics; these are not Turing-machine state counts."""
from pathlib import Path
import json
from syntax import *
from prior_templates import axioms as old_axioms


def hull_axioms() -> dict[str, F]:
    # Matrix Phi(x,y,p). Seed a and local bounds never occur free in it.
    a,v,x,y,b,z,p = range(7)
    phi = hole(x,y,p)
    def bounded(kernel: F) -> F:
        return all_(x,ex(b,all_(y,imp(phi,kernel))))
    exact = bex(b,v,all_(y,iff(mem(y,b),phi)))
    efh_body = all_(a,ex(v,and_(mem(a,v),ball(x,v,
                      and_(subset(x,v,z),exact)))))
    efh = all_(p,imp(bounded(subset(y,b,z)),efh_body))
    efh_member = all_(p,imp(bounded(mem(y,b)),efh_body))
    def closure(seed: F) -> F:
        return all_(a,ex(v,and_(seed,ball(x,v,
                          all_(y,imp(phi,mem(y,v)))))))
    tc = all_(p,imp(bounded(mem(y,b)),closure(subset(a,v,z))))
    tc_root = all_(p,imp(bounded(mem(y,b)),closure(mem(a,v))))
    sc_root = all_(p,imp(bounded(subset(y,b,z)),closure(mem(a,v))))
    sep = alls([p,a],ex(b,all_(y,iff(mem(y,b),
                            and_(mem(y,a),hole(y,p))))))
    power = all_(a,ex(b,all_(y,iff(mem(y,b),subset(y,a,z)))))
    return dict(EFH=efh,EFH_member_only=efh_member,TC_element_seed=tc,
                TC_rooted=tc_root,SC_rooted=sc_root,Separation=sep,Power=power)


def run() -> dict:
    aa = old_axioms() | hull_axioms()
    data = {k: metrics(f) | {'alpha_variable_labels': metrics(alpha_reuse(f))['variable_labels']}
            for k,f in aa.items()}
    groups = {
        'Ext_EFH':['Ext','EFH'], 'EC_EFH':['EC','EFH'],
        'Ext_Sep_Power_TC':['Ext','Separation','Power','TC_element_seed'],
        'Ext_Sep_SC':['Ext','Separation','SC_rooted'],
        'Ext_CP_SBI':['Ext','CP','SBI'], 'EC_CP_GIC':['EC','CP','GIC'],
        'RCC':['CP','GIC']}
    data['_groups']={k:sum(data[t]['nodes'] for t in ts) for k,ts in groups.items()}
    data['_scope']='Basis: membership, equality, negation, implication, forall. Holes are leaves. One explicit parameter; SBI/GIC also allow their domain as a matrix argument. No variable-code, logic, checker, or TM-backend cost.'
    out=Path(__file__).resolve().parents[1]/'results'
    out.mkdir(exist_ok=True)
    (out/'template_metrics.json').write_text(json.dumps(data,indent=2)+'\n')
    (out/'expanded_templates.txt').write_text('\n\n'.join(k+'\n'+pretty(alpha_reuse(f)) for k,f in aa.items())+'\n')
    print(json.dumps(data,indent=2))
    return data

if __name__=='__main__': run()
