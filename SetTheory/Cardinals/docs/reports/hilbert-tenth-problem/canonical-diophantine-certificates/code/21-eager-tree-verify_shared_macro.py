#!/usr/bin/env python3
"""Separate read-only verifier of the exported symbolic kernel proofs.
Imports neither compiler nor experimental evaluator. Standard library only.
"""
from pathlib import Path
import json

def verify(path):
    data=json.loads(Path(path).read_text());nodes=data['nodes'];names=data['names']
    assert data['format']=='original-jay-symbolic-application-dag-v1'
    seen=set();bounds=[];lower=[]
    for i,n in enumerate(nodes):
        assert tuple(n) not in seen;seen.add(tuple(n))
        assert n[0] in ['L','S','F','X']
        arity={'L':0,'S':1,'F':2,'X':0}[n[0]]
        assert len(n)==arity+1
        assert all(type(j) is int and 0<=j<i for j in n[1:])
        if n[0]=='L': b=(0,0);lo=0
        elif n[0]=='X':b=(1,0);lo=None
        elif n[0]=='S':
            a,c=bounds[n[1]];b=(a,c+1);lo=None if lower[n[1]] is None else lower[n[1]]+1
        else:
            a,c=bounds[n[1]];d,e=bounds[n[2]];b=(2*max(a,d),2*max(c,e)+3)
            lo=None if any(lower[j] is None for j in n[1:]) else max(2,2*max(lower[j] for j in n[1:])-1)
        bounds.append(b);lower.append(lo)
    assert nodes[names['SX']]==['S',names['X']]
    assert nodes[names['SSX']]==['S',names['SX']]
    assert nodes[names['L']]==['L']
    literal_path=Path(path).with_name('shared_compression_program.json')
    literal=json.loads(literal_path.read_text())
    assert literal['format']=='original-jay-tree-value-dag-v1'
    todo=[(names['R'],literal['root'])]; compared=set()
    while todo:
        i,j=todo.pop()
        if (i,j) in compared: continue
        compared.add((i,j)); left,right=nodes[i],literal['nodes'][j]
        assert left[0]==right[0] and len(left)==len(right)
        assert left[0] in ['L','S','F']
        todo.extend(zip(left[1:],right[1:]))
    byname={}
    for case in data['cases']:
        rows=case['rows'];assert rows
        oracle_count=0
        for i,r in enumerate(rows):
            assert all(type(r[k]) is int and 0<=r[k]<len(nodes) for k in ['x','y','z'])
            assert len(r['cost'])==2 and all(type(z) is int and z>=0 for z in r['cost'])
            assert all(type(p) is int and 0<=p<len(rows) for p in r['premises'])
            x,y,z=r['x'],r['y'],r['z'];c=r['cost'];ps=[rows[j] for j in r['premises']]
            if r['oracle']:
                oracle_count+=1;assert case['name']=='step'
                assert (x,y,z)==(names['R'],names['SX'],names['I']) and c==[1,0] and not ps
                continue
            n=nodes[x]
            if n[0]=='L':assert not ps and nodes[z]==['S',y]
            elif n[0]=='S':assert not ps and nodes[z]==['F',n[1],y]
            else:
                assert n[0]=='F';left,b=n[1:];m=nodes[left]
                if m[0]=='L':assert not ps and z==b
                elif m[0]=='S':
                    assert len(ps)==3;a=m[1];u=ps[0]['z'];v=ps[1]['z']
                    assert [(p['x'],p['y'],p['z']) for p in ps]==[(b,y,u),(a,y,v),(u,v,z)]
                else:
                    assert m[0]=='F' and len(ps)==2;a,b=m[1:];u=ps[0]['z']
                    assert [(p['x'],p['y'],p['z']) for p in ps]==[(y,a,u),(u,b,z)]
            assert c==[sum(p['cost'][0] for p in ps),1+sum(p['cost'][1] for p in ps)]
            assert all(sum(c)>sum(p['cost']) for p in ps)
        r=rows[0];assert r['x']==names['R'] and r['z']==names['I']
        if case['name']=='base0': assert r['y']==names['L'] and r['cost']==[0,94]
        elif case['name']=='base1':assert nodes[r['y']]==['S',names['L']] and r['cost']==[0,656]
        else:assert case['name']=='step' and r['y']==names['SSX'] and r['cost']==[2,468]
        assert oracle_count==int(case['name']=='step')
        used=[r[k] for r in rows for k in ['x','y','z']]
        byname[case['name']]=dict(rows=len(rows),root_cost=r['cost'],
            scalar_bit_bound=[max(bounds[j][0] for j in used),max(bounds[j][1] for j in used)])
    assert set(byname)=={'base0','base1','step'}
    assert bounds[names['R']][0]==0
    return dict(status='all explicit symbolic inference rows and affine costs verified',cases=byname,
                program_scalar_bits_lower=lower[names['R']],program_scalar_bits_upper=bounds[names['R']][1])

if __name__=='__main__':
    here=Path(__file__).resolve().parent
    result=verify(here/'shared_symbolic_proofs.json')
    print(json.dumps(result,indent=2))
