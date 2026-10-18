#!/usr/bin/env python3
"""Stdlib-only exact verification of the supplied register-program certificate.

Run: python verify.py
This verifies a register-program equivalence for every register file. It is
not a Turing-machine simulator or a claim of a new state-count record.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json,hashlib

HERE=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError('Run without -O: this certificate checker requires assertions.')

def program(path):
    data=json.loads(path.read_text())
    nodes={int(n):tuple(tuple(e) for e in p) for n,p in data['nodes'].items()}
    root=data['root']
    assert set(nodes)==set(range(len(nodes))) and root in nodes
    active=set();seen=set()
    def visit(n):
        assert n not in active,'cyclic decoder'
        if n in seen:return
        active.add(n)
        assert len(nodes[n])==2
        for e in nodes[n]:
            assert e and e[0] in {'N','I','D','B','C','H'}
            assert len(e)==(1 if e[0]=='H' else 2)
            if e[0]=='N':assert e[1] in nodes;visit(e[1])
            elif e[0] in {'I','D'}:assert isinstance(e[1],int) and 0<=e[1]<9
            elif e[0] in {'B','C'}:assert isinstance(e[1],int) and e[1]>0
        active.remove(n);seen.add(n)
    visit(root)
    assert len(seen)==len(nodes),'unreachable serialized node'
    return nodes,root

def site(nodes,root,path):
    n=root;i=0
    while True:
        e=nodes[n][int(path[i]) if i<len(path) else 0];i+=1
        if e[0]!='N':return e,(path+'0'*i)[:i]
        n=e[1]

def advance(path):
    return format((int(path or '0',2)+1)%(2**len(path)),f'0{len(path)}b') if path else ''

def strip(path,symbol,k):
    i=len(path)
    while i and k:
        i-=1;k-=path[i]==symbol
    return path[:i]

def nextpc(op,path,nonzero=True):
    tag=op[0]
    if tag=='I' or (tag=='D' and nonzero):return advance(path)
    if tag=='B' or tag=='D':return advance(strip(path,'0',op[1] if tag=='B' else 1))
    if tag=='C':return strip(path,'1',op[1])
    raise AssertionError('halt has no successor')

def segment(nodes,root,path):
    increments=Counter()
    for steps in range(1000):
        op,full=site(nodes,root,path)
        if op[0] in 'DH':return increments,path,steps
        if op[0]=='I':increments[op[1]]+=1
        path=nextpc(op,full)
    raise AssertionError('segment fuel exhausted')

def check(p1,p2,cert):
    n1,r1=p1;n2,r2=p2;longest=0
    def branch(a,b,j):
        nonlocal longest
        if not isinstance(j,int) or not 0<=j<len(cert):return False
        ia,pa,sa=segment(n1,r1,a);ib,pb,sb=segment(n2,r2,b)
        longest=max(longest,sa,sb)
        return ia==ib and (pa,pb)==tuple(cert[j][:2])
    assert cert and branch('','',0),'initial segment mismatch'
    for a,b,j,k in cert:
        assert isinstance(a,str) and isinstance(b,str)
        assert set(a)<=set('01') and set(b)<=set('01')
        ea,qa=site(n1,r1,a);eb,qb=site(n2,r2,b)
        if ea==eb==('H',):continue
        assert ea==eb and ea[0]=='D','different tests'
        assert branch(nextpc(ea,qa,True),nextpc(eb,qb,True),j),'nonzero branch mismatch'
        assert branch(nextpc(ea,qa,False),nextpc(eb,qb,False),k),'zero branch mismatch'
    return longest

def metrics(p):
    nodes,root=p
    @lru_cache(None)
    def go(e):
        if e[0]!='N':return (0,0,0,1,e[1] if e[0]=='B' else int(e[0]=='D'),e[1] if e[0]=='C' else 0)
        a,b=map(go,nodes[e[1]])
        prefix=1+a[0]
        return prefix,max(prefix,a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3],max(a[4]-1,b[4]),max(a[5],b[5]-1)
    _,zero,depth,leaves,brk,cont=go(('N',root))
    assert brk==cont==0,'escaping root control'
    return {'decoder_nodes':len(nodes),'maximum_zero_run':zero,'depth':depth,'leaf_count':leaves}

def main():
    baseline=program(HERE/'baseline_dag.json');candidate=program(HERE/'candidate_dag.json')
    cert=json.loads((HERE/'bisimulation_certificate.json').read_text())
    a=check(baseline,candidate,cert)
    b=check(candidate,baseline,[[y,x,j,k] for x,y,j,k in cert])
    wrong=[list(row) for row in cert];wrong[0][0]='1'+wrong[0][0]
    rejected=False
    try:check(baseline,candidate,wrong)
    except AssertionError:rejected=True
    assert rejected,'corruption check failed'
    result={'baseline':metrics(baseline),'candidate':metrics(candidate),
            'certificate_entries':len(cert),'forward':True,'backward':True,
            'maximum_segment':max(a,b),'malformed_initial_path_rejected':rejected,
            'scope':'RM halting equivalence for every initial register file; not a TM state count',
            'sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in
                      ('baseline_dag.json','candidate_dag.json','bisimulation_certificate.json')}}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
