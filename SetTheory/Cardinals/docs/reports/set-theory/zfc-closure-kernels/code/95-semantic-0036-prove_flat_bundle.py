#!/usr/bin/env python3
"""Produce K/S-only proof certificates of negative-conjunction flattening.

The replay checker verifies only exact K,S substitution instances and MP.
It does not invoke a truth table, classicality, ex falso or a trusted
deduction-theorem implementation. F is an arbitrary formula parameter.
"""
from pathlib import Path
import json
import prove_ksp_lukasiewicz as h

C=h.C
A,B,D,E,F='A','B','C','D','F'
def andf(*xs):
    out=F
    for x in reversed(xs):out=C(x,out)
    return C(out,F)
AB=andf(A,B)
DE=andf(D,E)
old=andf(AB,DE)
flat=andf(A,B,D,E)

def application(p,*qs):
    for q in qs:p=h.mp(p,q)
    return p

def abstract(xs,p):
    for x in reversed(xs):p=h.discharge(x,p)
    return p

def nested_to_flat():
    k=C(A,C(B,C(D,C(E,F))))
    f=application(h.assumption(k),*[h.assumption(x) for x in (A,B,D,E)])
    f=application(h.assumption(DE),abstract((D,E),f))
    f=application(h.assumption(AB),abstract((A,B),f))
    f=application(h.assumption(old),abstract((AB,DE),f))
    return abstract((old,k),f)

def flat_to_nested():
    k=C(AB,C(DE,F))
    kab=C(A,C(B,F))
    kde=C(D,C(E,F))
    pab=abstract((kab,),application(h.assumption(kab),h.assumption(A),h.assumption(B)))
    pde=abstract((kde,),application(h.assumption(kde),h.assumption(D),h.assumption(E)))
    f=application(h.assumption(k),pab,pde)
    f=application(h.assumption(flat),abstract((A,B,D,E),f))
    return abstract((flat,k),f)

def certificate(p):
    active=set()
    def visit(i):
        if i in active:return
        active.add(i)
        for q in h.nodes[i]['premises']:visit(q)
    visit(p)
    order=sorted(active)
    remap={old:new for new,old in enumerate(order)}
    rows=[]
    for i in order:
        row=h.nodes[i].copy()
        assert row['rule'] in ('K','S','MP')
        row['premises']=[remap[q] for q in row['premises']]
        row['pretty']=h.pretty(row['conclusion'])
        rows.append(row)
    return dict(final=remap[p],nodes=rows)

def check(cert, goal):
    conclusions=[]
    counts={}
    for i,row in enumerate(cert['nodes']):
        rule=row['rule']
        f=h.freeze(row['conclusion'])
        args=h.freeze(row['parameters'])
        refs=row['premises']
        if rule in ('K','S'):
            assert refs==[]
            assert f==dict(K=h.K,S=h.S)[rule](*args)
        elif rule=='MP':
            assert len(refs)==2 and all(0<=q<i for q in refs)
            major,minor=(conclusions[q] for q in refs)
            assert major==C(minor,f)
        else:raise AssertionError('Forbidden rule: '+rule)
        conclusions.append(f)
        counts[rule]=counts.get(rule,0)+1
    assert conclusions[cert['final']]==goal
    return dict(status='PASS',proof_nodes=len(conclusions),rule_counts=counts,
                assumptions=0,arbitrary_formula_parameters=['A','B','C','D','F'])

def main():
    proofs=dict(nested_to_flat=certificate(nested_to_flat()),flat_to_nested=certificate(flat_to_nested()))
    base=Path(__file__).resolve().parent
    path=base/'flat_bundle_equivalence.json'
    path.write_text(json.dumps(proofs,indent=2)+'\n')
    replay=json.loads(path.read_text())
    result=dict(nested_to_flat=check(replay['nested_to_flat'],C(old,flat)),
                flat_to_nested=check(replay['flat_to_nested'],C(flat,old)))
    (base/'flat_bundle_equivalence_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
