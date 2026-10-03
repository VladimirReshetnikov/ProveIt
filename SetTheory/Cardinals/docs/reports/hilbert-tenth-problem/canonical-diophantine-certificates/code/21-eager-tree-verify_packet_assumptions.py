#!/usr/bin/env python3
"""Read-only checks needed to identify the template union with the canonical DAG.
Independently implements the five application cases; no frozen code imports.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKET = HERE

def verify(packet=PACKET):
    path=packet/'shared_symbolic_proofs.json'
    data=json.loads(path.read_text());ns=data['nodes'];names=data['names']
    assert data['format']=='original-jay-symbolic-application-dag-v1'
    seen=set();deps=[]
    for i,r in enumerate(ns):
        assert r[0] in ['L','S','F','X']
        assert len(r)=={'L':1,'S':2,'F':3,'X':1}[r[0]]
        assert all(type(j) is int and 0<=j<i for j in r[1:])
        assert tuple(r) not in seen;seen.add(tuple(r))
        deps.append(r[0]=='X' or any(deps[j] for j in r[1:]))
    assert ns[names['L']]==['L']
    assert ns[names['X']]==['X']
    assert ns[names['SX']]==['S',names['X']]
    assert ns[names['SSX']]==['S',names['SX']]
    assert not deps[names['R']] and not deps[names['I']]
    literal_path=packet/'shared_compression_program.json'
    literal=json.loads(literal_path.read_text());ln=literal['nodes']
    assert literal['format']=='original-jay-tree-value-dag-v1'
    for i,r in enumerate(ln):
        assert r[0] in ['L','S','F']
        assert len(r)=={'L':1,'S':2,'F':3}[r[0]]
        assert all(type(j) is int and 0<=j<i for j in r[1:])
    work=[(names['R'],literal['root'])];compared=set()
    while work:
        i,j=work.pop()
        if (i,j) in compared:continue
        compared.add((i,j));x,y=ns[i],ln[j]
        assert x[0]==y[0] and len(x)==len(y)
        work.extend(zip(x[1:],y[1:]))
    cases={}
    for case in data['cases']:
        name=case['name'];rs=case['rows'];assert name not in cases
        assert len(set((r['x'],r['y']) for r in rs))==len(rs)
        oracle_ids=[]
        for i,r in enumerate(rs):
            assert all(type(r[k]) is int and 0<=r[k]<len(ns) for k in ['x','y','z'])
            assert all(type(p) is int and 0<=p<len(rs) for p in r['premises'])
            assert len(r['cost'])==2 and all(type(z) is int and z>=0 for z in r['cost'])
            x,y,z=r['x'],r['y'],r['z'];ps=[rs[p] for p in r['premises']]
            if r['oracle']:
                oracle_ids.append(i)
                assert name=='step'
                assert (x,y,z)==(names['R'],names['SX'],names['I'])
                assert not ps and r['cost']==[1,0]
                continue
            if ns[x][0]=='L':assert not ps and ns[z]==['S',y]
            elif ns[x][0]=='S':assert not ps and ns[z]==['F',ns[x][1],y]
            else:
                assert ns[x][0]=='F'
                left,b=ns[x][1:];q=ns[left]
                if q[0]=='L':assert not ps and z==b
                elif q[0]=='S':
                    assert len(ps)==3
                    a=q[1];u=ps[0]['z'];v=ps[1]['z']
                    assert [(p['x'],p['y'],p['z']) for p in ps]==[(b,y,u),(a,y,v),(u,v,z)]
                else:
                    assert q[0]=='F' and len(ps)==2
                    a,b=q[1:];u=ps[0]['z']
                    assert [(p['x'],p['y'],p['z']) for p in ps]==[(y,a,u),(u,b,z)]
            assert r['cost']==[sum(p['cost'][0] for p in ps),1+sum(p['cost'][1] for p in ps)]
            assert all(sum(r['cost'])>sum(p['cost']) for p in ps)
        reached=set();todo=[0]
        while todo:
            i=todo.pop()
            if i in reached:continue
            reached.add(i);todo.extend(rs[i]['premises'])
        assert reached==set(range(len(rs)))
        root=rs[0]
        assert (root['x'],root['z'])==(names['R'],names['I'])
        if name=='base0':assert root['y']==names['L'] and root['cost']==[0,94] and not oracle_ids
        elif name=='base1':assert ns[root['y']]==['S',names['L']] and root['cost']==[0,656] and not oracle_ids
        else:assert name=='step' and root['y']==names['SSX'] and root['cost']==[2,468] and len(oracle_ids)==1
        if name!='step':assert all(not deps[r[k]] for r in rs for k in ['x','y','z'])
        cases[name]={'rows':len(rs),'reachable_rows':len(reached),'distinct_symbolic_pairs':len(rs),'oracle_rows':oracle_ids,'root_cost':root['cost']}
    assert set(cases)=={'base0','base1','step'}
    assert cases['base0']['rows']==44 and cases['base1']['rows']==179 and cases['step']['rows']==150
    return dict(status='all kernel rows, root reachability, pair uniqueness, and literal identity verified',
        cases=cases,source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [path,literal_path]})

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=PACKET,help='directory containing the two frozen JSON inputs')
    args=parser.parse_args()
    result=verify(args.packet);(HERE/'packet_assumptions_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
