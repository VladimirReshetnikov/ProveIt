#!/usr/bin/env python3
"""Replace eligible two-alias dummy cycles by unit-coefficient quartics."""
from collections import Counter
from copy import deepcopy


def compress_pairs(artifact,certificate):
    p=deepcopy(artifact);c=deepcopy(certificate)
    terms={tuple(m):a for a,m in p['terms']}
    removed=set();replaced=[]
    for cy in c['equality_cycles']:
        av=cy['aliases'];cy['method']='cycle'
        if len(av)!=3:continue
        ds=[v for v in av if p['variables'][v]['kind']=='equality_dummy']
        if len(ds)!=1:continue
        d=ds[0];a,b=[v for v in av if v!=d]
        delta=Counter()
        for v in av:delta[(v,v)]-=1
        for x,y in zip(av,av[1:]+av[:1]):delta[tuple(sorted((x,y)))]+=1
        for val,m in [(1,(a,a,a,a)),(1,(b,b,b,b)),(-1,(a,a,a,b)),(-1,(a,b,b,b))]:delta[tuple(sorted(m))]+=val
        if any(abs(terms.get(m,0)+v)>1 for m,v in delta.items()):continue
        for m,v in delta.items():
            n=terms.get(m,0)+v
            if n:terms[m]=n
            else:terms.pop(m,None)
        cy['aliases']=[a,b];cy['method']='quartic_pair';removed.add(d)
        replaced.append({'logical_variable':cy['normalized_variable'],'old_aliases':av,'new_aliases':[a,b]})
    rename={v:i for i,v in enumerate(v for v in range(len(p['variables'])) if v not in removed)}
    p['variables']=[v for i,v in enumerate(p['variables']) if i not in removed]
    terms={tuple(rename[v] for v in m):a for m,a in terms.items()}
    for e in c['edges']:e['monomial']=[rename[v] for v in e['monomial']]
    for prod in c.get('products',[]):prod['factors']=[rename[v] for v in prod['factors']]
    for cy in c['equality_cycles']:cy['aliases']=[rename[v] for v in cy['aliases']]
    c['unit_path']=[rename[v] for v in c['unit_path']]
    c['quartic_pair_compression']={'removed_dummy_count':len(removed),'replacements_before_renumbering':replaced,
        'renaming':[[v,rename[v]] for v in sorted(rename)]}
    if 'alias_quotient' in c:
        c['alias_quotient']['mapping']=[[old,rename[new]] for old,new in c['alias_quotient']['mapping']]
    p['terms']=[[terms[m],list(m)] for m in sorted(terms,key=lambda m:(len(m),m))]
    p['metrics'].update({'variables':len(p['variables']),'monomials':len(terms),
        'quartic_pair_equalities':len(removed),
        'equality_dummies':sum(v['kind']=='equality_dummy' for v in p['variables']),
        'positive_coefficients':sum(a>0 for a in terms.values()),'negative_coefficients':sum(a<0 for a in terms.values())})
    p['schema']='support-aware-graph-quartic-v2'
    return p,c
