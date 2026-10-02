#!/usr/bin/env python3
"""Independently verify JSON polynomial exports; does not import the compiler."""
from pathlib import Path
from collections import defaultdict
from math import prod
import argparse, json

def aff(e):
    return {():e['constant'], **{(v,):a for v,a in e['terms'].items()}}

def add_product(p,a,b):
    for u,x in a.items():
        for v,y in b.items(): p[tuple(sorted(u+v))]+=x*y

def verify(path):
    d=json.loads(path.read_text())
    if 'expanded_polynomial' not in d: return None
    names=d['parameters']+d['witnesses']; values=d['assignment']
    assert len(names)==len(set(names)) and set(names)==set(values)
    assert all(type(v) is int and v>=0 for v in values.values())
    p=defaultdict(int)
    for e in d['affine_residuals']:
        a=aff(e); add_product(p,a,a)
    for a,b in d['nonnegative_products']:
        a,b=aff(a),aff(b)
        assert all(x>=0 for x in a.values()) and all(x>=0 for x in b.values())
        add_product(p,a,b)
    p={k:v for k,v in p.items() if v}
    emitted={}
    for term in d['expanded_polynomial']:
        k=tuple(term['variables']); v=term['coefficient']
        assert k==tuple(sorted(k)) and len(k)<=2 and k not in emitted
        assert type(v) is int and v!=0 and set(k)<=set(names)
        emitted[k]=v
    assert emitted==p
    value=sum(c*prod(values[v] for v in k) for k,c in p.items())
    assert value==0==d['polynomial_value']
    assert len(p)==d['counts']['expanded_monomials']
    return {'file':path.name,'status':'PASS','witnesses':len(d['witnesses']),
            'monomials':len(p),'degree':max(map(len,p),default=0),'value':value}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files',nargs='*',type=Path)
    args=parser.parse_args()
    paths=args.files or [p for p in sorted((Path(__file__).resolve().parents[1]/'results').glob('*.json'))
                            if p.name not in {'test_receipt.json','export_verification.json'}]
    receipt=[r for p in paths if (r:=verify(p)) is not None]
    assert receipt, 'No polynomial exports supplied'
    print(json.dumps({'status':'PASS','exports':receipt},indent=2))
