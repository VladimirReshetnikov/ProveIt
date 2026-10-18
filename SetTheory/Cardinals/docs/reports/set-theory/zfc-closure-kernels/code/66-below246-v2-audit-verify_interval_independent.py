#!/usr/bin/env python3
"""Check a finite interval certificate using Jeff's independent RM path mirror.

No worklist or capped-domain transfer is imported. Each edge uses the exact
integer interval image, with None denoting an unbounded upper endpoint.
"""
from pathlib import Path
import hashlib, json, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'search/decoder'))
import explore as e

def contains(outer,inner):
    return outer[0]<=inner[0] and (outer[1] is None or (inner[1] is not None and inner[1]<=outer[1]))

def validate(data):
    assert data['domain']==dict(lower_cap=8,infinity_code=9)
    raw=data['invariants']
    assert len(raw)==len(e.SITES)==6460
    inv=[]
    for row in raw:
        if row is None:inv.append(None);continue
        assert len(row)==9
        converted=[]
        for lo,hi in row:
            assert type(lo)==type(hi)==int and 0<=lo<=8 and lo<=hi<=9
            converted.append((lo,None if hi==9 else hi))
        inv.append(converted)
    index={p:i for i,(p,_,_)in enumerate(e.SITES)}
    def locate(P):
        edge,Q=e.rmpath.site(e.ORIGINAL,P)
        assert all(not b for b in P[len(Q):])
        word=''.join('1'if b else'0'for b in Q)
        return index[word]
    initial=(3,0,0,0,3,0,0,0,0)
    start=locate([])
    assert inv[start] is not None
    assert all(contains(a,(v,v))for a,v in zip(inv[start],initial))
    edge_count=0
    for i,((pc,op,r),v)in enumerate(zip(e.SITES,inv)):
        if v is None:continue
        P=[b=='1'for b in pc]
        transfers=[]
        if op=='CH':continue
        if op=='CB':transfers.append((e.rmpath.brk(r,P),v))
        elif op=='CC':transfers.append((e.rmpath.cont(r,P),v))
        elif op=='CI':
            lo,hi=v[r];w=v.copy();w[r]=(lo+1,None if hi is None else hi+1)
            transfers.append((e.rmpath.inc_path(P),w))
        else:
            assert op=='CD'
            lo,hi=v[r]
            if lo==0:
                w=v.copy();w[r]=(0,0)
                transfers.append((e.rmpath.brk(1,P),w))
            if hi is None or hi>0:
                w=v.copy();w[r]=(max(lo,1)-1,None if hi is None else hi-1)
                transfers.append((e.rmpath.inc_path(P),w))
        for P,w in transfers:
            j=locate(P)
            assert inv[j]is not None,('missing successor',i,j)
            assert all(contains(a,b)for a,b in zip(inv[j],w)),('closure',i,j,w,inv[j])
            edge_count+=1
    return dict(status='PASS',reachable_sites=sum(v is not None for v in inv),closure_edges=edge_count,
        method='Exact interval images, unbounded integer endpoints, independent Jeff RM path semantics')

def main():
    assert __debug__
    source=Path(sys.argv[1])if len(sys.argv)>1 else HERE.parent/'results/interval-invariants.json'
    data=json.loads(source.read_text())
    result=validate(data)
    # The initial condition must reject a vacuous all-unreachable certificate.
    false=dict(data,invariants=[None]*6460)
    try:validate(false)
    except AssertionError:result['all_unreachable_mutation']='REJECTED'
    else:raise AssertionError('unsound vacuous certificate accepted')
    # Removing a live non-initial successor must violate closure.
    index=next(i for i,v in enumerate(data['invariants'])if v is not None and i!=0)
    broken=list(data['invariants']);broken[index]=None
    try:validate(dict(data,invariants=broken))
    except AssertionError:result['missing_live_successor_mutation']='REJECTED'
    else:raise AssertionError('missing live successor accepted')
    result['invariant_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
    (HERE/'interval-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
