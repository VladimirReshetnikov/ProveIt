#!/usr/bin/env python3
"""Independent unbounded-tape startup and literal-table checks.

Only JSON data and literal transitions are read. No constructor is imported.
"""
from pathlib import Path
import collections,hashlib,json
HERE=Path(__file__).resolve().parent
PHY=(6,2,0,4,3,7,8,5,1)
def rows(path):
    out={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in out and b in(0,1) and w in(0,1) and d in('L','R')
        out[q,b]=(w,d,t)
    return out
def check(path):
    native=rows(path/'machine.native.tm');dense=rows(path/'machine.tm')
    states={q for q,b in native};assert len(states)==194 and len(native)==388
    assert set(native)=={(q,b)for q in states for b in(0,1)}
    assert {t for w,d,t in native.values()}-states=={254}
    assert set(dense)=={(q,b)for q in range(194)for b in(0,1)}
    labels=json.loads((path/'labels.json').read_text());assert len(labels)==len(set(labels))==195
    assert (labels[0],labels[-1])==(74,254)
    assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==native
    reachable={74};queue=[74]
    for q in queue:
        for b in(0,1):
            t=native[q,b][2]
            if t!=254 and t not in reachable:reachable.add(t);queue.append(t)
    assert reachable==states
    site=json.loads((path/'sites.json').read_text())[25][0]
    steps=json.loads((path/'receipt.json').read_text())['startup']['steps']
    ones=set();q=74;head=0;visits=collections.Counter()
    for _ in range(steps):
        assert q!=254
        b=int(head in ones);visits[q,b]+=1;w,d,q=native[q,b]
        (ones.add if w else ones.discard)(head);head+=1 if d=='R'else-1
    assert (q,head)==(84,-2)
    logical=[2]+[0]*8;physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    expected={head-1,head+48}|{head+i for i,b in enumerate(site) if b=='1'}
    cursor=head+49
    for v in physical+[1]*26:
        cursor+=1;expected.update(range(cursor,cursor+v+1));cursor+=v+1
    assert ones==expected
    sha=lambda f:hashlib.sha256((path/f).read_bytes()).hexdigest()
    return {'family':path.name,'status':'PASS','states':194,'rows':388,'graph_reachable':194,'start':0,'halt':194,'native_start':74,'native_halt':254,'steps':steps,'complete_tape_equality':True,'unbounded_integer_tape_coordinates':True,'head':head,'state':q,'one_cells':sorted(ones),'dense_sha256':sha('machine.tm'),'native_sha256':sha('machine.native.tm'),'startup_row_uses':[[q,b,n]for(q,b),n in sorted(visits.items())]}
if __name__=='__main__':
    result=[check(HERE/'inputs'/n)for n in('GD194sum','GD194H','GD194HS')]
    (HERE/'startup_unbounded.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([{k:r[k]for k in('family','status','states','rows','steps','complete_tape_equality')}for r in result],indent=2))
