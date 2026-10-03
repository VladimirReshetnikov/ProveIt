#!/usr/bin/env python3
"""Independent checker for the serialized quadratic systems and quartics.
Does not import the compiler or witness constructor.
"""
from __future__ import annotations
from collections import defaultdict
from pathlib import Path
import json

def parse(terms):
    ans={}
    for item in terms:
        m=tuple(item['monomial']); c=item['coefficient']
        if type(c) is not int or c==0 or tuple(sorted(m))!=m or m in ans:
            raise ValueError('noncanonical sparse polynomial')
        ans[m]=c
    return ans

def evaluate(poly,env):
    s=0
    for mon,c in poly.items():
        term=c
        for variable in mon: term*=env[variable]
        s+=term
    return s

def check(path):
    obj=json.loads(path.read_text()); env=obj['witness']
    names=obj['source_variables']+obj['auxiliary_variables']
    assert len(names)==len(set(names)) and set(names)==set(env)
    assert all(type(v) is int and v>=0 for v in env.values())
    residuals=[parse(p) for p in obj['equations']]
    assert all(max(map(len,p),default=0)<=2 for p in residuals)
    expected=defaultdict(int)
    for p in residuals:
        for a,c in p.items():
            for b,d in p.items(): expected[tuple(sorted(a+b))]+=c*d
    expected={m:c for m,c in expected.items() if c}
    actual=parse(obj['quartic']); assert actual==expected
    assert max(map(len,actual),default=0)==obj['degree']<=4
    assert all(evaluate(p,env)==0 for p in residuals)
    assert evaluate(actual,env)==0
    rejected=0
    for v in obj['auxiliary_variables']:
        env[v]+=1
        assert evaluate(actual,env)>0
        env[v]-=1; rejected+=1
    return dict(file=path.name,variables=len(names),equations=len(residuals),
                degree=obj['degree'],monomials=len(actual),
                mutations_rejected=rejected,status='PASS')

if __name__=='__main__':
    data=Path(__file__).resolve().parents[1]/'data'
    result=[check(p) for p in sorted(data.glob('*_quartic.json'))]
    (data/'export_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
