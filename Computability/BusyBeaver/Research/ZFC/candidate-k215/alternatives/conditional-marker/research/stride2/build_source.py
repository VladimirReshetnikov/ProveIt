#!/usr/bin/env python3
"""Build five composite or direct S2 associations from the pinned MP0 source.

No optimization or physical allocation is performed. Python standard library
only. The input is MP0_Transfer_215/source/mp0-transfer201.sites.json.
"""
from __future__ import annotations
import argparse
from functools import cache
import hashlib
import json
from pathlib import Path

PARENT_SHA='8ddb942f0f1d8e2e3b12ab7217c7232eb553cd288fca38dbf9b0eded73893dd5'
PATH='110101'


def leaf(t):return isinstance(t[0],str)
def sites(t,p=''):
    return [[p,*t]] if leaf(t) else sites(t[0],p+'0')+sites(t[1],p+'1')
def tree(rows):
    d={p:(o,r) for p,o,r in rows}
    def f(p):return d[p] if p in d else (f(p+'0'),f(p+'1'))
    t=f('');assert sites(t)==rows;return t
def sub(t,p):
    for b in p:t=t[int(b)]
    return t
def replace(t,p,x):
    if not p:return x
    z=list(t);b=int(p[0]);z[b]=replace(z[b],p[1:],x);return tuple(z)
@cache
def boundary(t):
    if leaf(t):
        o,r=t
        return (1,0,o=='CH') if o=='CD' else (r,0,False) if o=='CB' else (0,r,False) if o=='CC' else (0,0,o=='CH')
    a,b=boundary(t[0]),boundary(t[1])
    return max(a[0]-1,0,b[0]),max(a[1],b[1]-1,0),a[2] or b[2]
def metrics(t):
    seen=set()
    def f(n):
        if n in seen:return
        seen.add(n)
        if not leaf(n):f(n[0]);f(n[1])
    f(t);ss=sites(t)
    return {'dag_nodes':len(seen),'leaf_occurrences':len(ss),
            'maximum_depth':max(len(p) for p,o,r in ss),
            'maximum_zero_run':max(len(z) for p,o,r in ss for z in p.split('1')),
            'guards':sum(2 if o=='CD' else 1 for p,o,r in ss)}
def graph(rows):
    idx={p:i for i,(p,o,r) in enumerate(rows)}; intervals={};n=len(rows)
    def visit(p):
        if p in idx:q=(idx[p],idx[p]+1)
        else:
            a,b=visit(p+'0'),visit(p+'1');assert a[1]==b[0];q=(a[0],b[1])
        intervals[p]=q;return q
    visit('')
    def cut(p,b,k):
        for j in range(len(p)-1,-1,-1):
            if p[j]==b:
                k-=1
                if k==0:return intervals[p[:j]][1 if b=='0' else 0]%n
        return 0
    out=[]
    for i,(p,o,r) in enumerate(rows):
        targets=[(i+1)%n] if o=='CI' else [cut(p,'0',1),(i+1)%n] if o=='CD' else [cut(p,'0',r)] if o=='CB' else [cut(p,'1',r)] if o=='CC' else []
        out.append((o,r,targets))
    return out
def graph_binary(rows):
    idx={p:i for i,(p,o,r) in enumerate(rows)};depth=max(map(len,idx))
    def locate(p):
        word=p+'0'*depth
        for k in range(1,depth+1):
            if word[:k] in idx:
                assert '1' not in p[k:]
                return idx[word[:k]]
        raise AssertionError(p)
    def inc(p):return '' if not p else format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')
    def cut(p,b,k):
        positions=[i for i,z in enumerate(p) if z==b]
        return p[:positions[-k]] if len(positions)>=k else ''
    out=[]
    for p,o,r in rows:
        targets=[locate(inc(p))] if o=='CI' else [locate(inc(cut(p,'0',1))),locate(inc(p))] if o=='CD' else [locate(inc(cut(p,'0',r)))] if o=='CB' else [locate(cut(p,'1',r))] if o=='CC' else []
        out.append((o,r,targets))
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--direct',action='store_true',help='Build clearTop/loadH/NIP/NIP instead of DROP/NIP/NIP/NIP')
    a=ap.parse_args();raw=a.parent.read_bytes();assert hashlib.sha256(raw).hexdigest()==PARENT_SHA
    oldrows=json.loads(raw);old=tree(oldrows);oldgraph=graph(oldrows);assert oldgraph==graph_binary(oldrows)
    (D,N1),N2=sub(old,PATH);assert N1==N2;N=N1
    assert len(sites(D))==len(sites(N))==26
    assert boundary(D)==(0,0,False) and boundary(N)==(0,0,True)
    oldinside=[i for i,(p,o,r) in enumerate(oldrows) if p.startswith(PATH)]
    lo,hi=min(oldinside),max(oldinside)+1;assert hi-lo==78
    u,v=D,N
    if a.direct:
        u=(('CD',1),('CC',1));v=D[1]
        assert len(sites(v))==7 and boundary(u)==boundary(v)==(0,0,False)
    forms=[((u,v),(N,N)),(u,(v,(N,N))),(((u,v),N),N),((u,(v,N)),N),(u,((v,N),N))]
    a.out.mkdir(parents=True,exist_ok=False);results=[]
    for k,body in enumerate(forms):
        new=replace(old,PATH,body);rr=sites(new);g=graph(rr);assert g==graph_binary(rr)
        expected=[(o,r) for p,o,r in sites(u)]+[(o,r) for p,o,r in sites(v)]+[(o,r) for p,o,r in sites(N)]*2
        assert [(o,r) for p,o,r in sites(body)]==expected
        delta=len(sites(body))-(hi-lo)
        def mapidx(i):
            if i<lo:return i
            if i>=hi:return i+delta
            assert i==lo,('external edge into old macro interior',i)
            return lo
        retained=edges=0
        for i,(op,r,targets) in enumerate(oldgraph):
            if lo<=i<hi:continue
            j=mapidx(i);assert rr[j][1:]==oldrows[i][1:]
            assert g[j]==(op,r,[mapidx(z) for z in targets])
            retained+=1;edges+=len(targets)
        data=(json.dumps(rr,separators=(',',':'))+'\n').encode('ascii')
        filename=f'{"direct2" if a.direct else "stride2"}-{k}.sites.json';(a.out/filename).write_bytes(data)
        results.append({'file':filename,'sha256':hashlib.sha256(data).hexdigest(),
                        'metrics':metrics(new),'both_complete_CFGs_agree':True,
                        'retained_instructions':retained,'retained_edges':edges,
                        'changed_parent_interval':[lo,hi],'new_body_leaves':len(sites(body))})
    result={'status':'EXACT_STRIDE_TWO_SOURCE_PASS','parent_sha256':PARENT_SHA,
            'command':'direct clear/load/NIP/NIP' if a.direct else 'composite DROP/NIP/NIP/NIP',
            'command_tags':{'MP':0,'S2':1,'AX':'c+2'},'variants':results,
            'scope':'Literal source construction, closed command bodies, complete retained instruction/edge transport and two independent CFG resolvers; no physical machine.'}
    (a.out/'source_build.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
