#!/usr/bin/env python3
"""Rebuild the dominated command schedule and verify a retagged source.

All inputs are explicit files. Uses no search code or external modules.
This checks exact finite source structure and control flow, not the
mathematical macro contracts or a binary Turing-machine implementation.
"""
import argparse
import functools
import hashlib
import json
from pathlib import Path

def leaf(t): return isinstance(t[0],str)
def rows(t,p=''):
    return [(p,*t)] if leaf(t) else rows(t[0],p+'0')+rows(t[1],p+'1')
def parse(rr):
    trie={}
    for p,op,r in rr:
        t=trie
        for b in p:
            assert b in '01';t=t.setdefault(b,{})
        assert not t;t['leaf']=(op,r)
    def go(t):
        if 'leaf' in t:
            assert len(t)==1;return t['leaf']
        assert set(t)=={'0','1'};return go(t['0']),go(t['1'])
    t=go(trie);assert [list(r)for r in rows(t)]==rr
    return t
@functools.lru_cache(None)
def size(t): return 1 if leaf(t) else size(t[0])+size(t[1])
@functools.lru_cache(None)
def boundary(t):
    if leaf(t):
        op,r=t
        return (1,0) if op=='CD' else (r,0) if op=='CB' else (0,r) if op=='CC' else (0,0)
    a,b=boundary(t[0]),boundary(t[1])
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
def seq(ts):
    assert ts
    return ts[0] if len(ts)==1 else (ts[0],seq(ts[1:]))
def extract(tree,lo,hi):
    chunks=[]
    def walk(t,start):
        end=start+size(t)
        if end<=lo or hi<=start:return
        if lo<=start and end<=hi:
            assert boundary(t)==(0,0);chunks.append(t);return
        assert not leaf(t)
        walk(t[0],start);walk(t[1],start+size(t[0]))
    walk(tree,0);assert sum(map(size,chunks))==hi-lo
    return seq(chunks)
def construct(tree,read_b_at,common=False):
    assert read_b_at in (161,194,326)
    a=extract(tree,40,66);ra=extract(tree,23,37);rb=extract(tree,121,135)
    ranges={161:(161,194),194:(194,221),221:(221,247),326:(326,353)}
    edits={(23,37):None,(121,135):None,(161,194):a,
           (221,247):(ra,a),(4652,4678):(ra,a)}
    r=ranges[read_b_at]
    edits[r]=(rb,a if read_b_at==161 else extract(tree,*r))
    if common:
        edits={(121,135):None,(161,194):a,(194,221):(rb,(ra,extract(tree,194,221)))}
    used={}
    def walk(t,start):
        end=start+size(t)
        overlaps=[(r,v)for r,v in edits.items() if not(end<=r[0] or r[1]<=start)]
        if not overlaps:return t
        for (lo,hi),v in overlaps:
            if lo<=start and end<=hi:
                assert boundary(t)==(0,0)
                if start==lo:used[lo,hi]=used.get((lo,hi),0)+1;return v
                return None
        assert not leaf(t)
        a1=walk(t[0],start);b1=walk(t[1],start+size(t[0]))
        if a1 is None and b1 is not None:assert boundary(b1)==(0,0)
        if b1 is None and a1 is not None:assert boundary(a1)==(0,0)
        return b1 if a1 is None else a1 if b1 is None else(a1,b1)
    result=walk(tree,0)
    assert used=={r:1 for r in edits}
    return result
def structured_graph(tree):
    out=[];count=size(tree)
    def target(stack,k):return stack[k-1] if k<=len(stack) else 0
    def walk(t,i,breaks,continues):
        if leaf(t):
            op,r=t;nxt=(i+1)%count
            dest=(nxt,) if op=='CI' else (target(breaks,1),nxt) if op=='CD' else (target(breaks,r),) if op=='CB' else (target(continues,r),) if op=='CC' else ()
            assert op in ('CI','CD','CB','CC','CH')
            out.append((op,r,dest));return
        walk(t[0],i,((i+size(t))%count,)+breaks,continues)
        walk(t[1],i+size(t[0]),breaks,(i,)+continues)
    walk(tree,0,(),())
    return out
def counter_graph(rr):
    lookup={p:i for i,(p,op,r)in enumerate(rr)};depth=max(map(len,lookup))
    def dispatch(p):
        q=p+'0'*(depth+1)
        for k in range(1,len(q)+1):
            if q[:k]in lookup:
                assert '1'not in p[k:];return lookup[q[:k]]
        raise AssertionError('incomplete code tree')
    def successor(p):return format((int(p,2)+1)%2**len(p),f'0{len(p)}b') if p else ''
    def cut(p,bit,k):
        places=[i for i,b in enumerate(p)if b==bit]
        return p[:places[-k]] if len(places)>=k else ''
    out=[]
    for p,op,r in rr:
        dest=(dispatch(successor(p)),) if op=='CI' else (dispatch(successor(cut(p,'0',1))),dispatch(successor(p))) if op=='CD' else (dispatch(successor(cut(p,'0',r))),) if op=='CB' else (dispatch(cut(p,'1',r)),) if op=='CC' else ()
        out.append((op,r,dest))
    return out
def signature(g):
    return [(op,r if op in ('CI','CD','CH') else None,dest) for op,r,dest in g]
def metrics(t):
    seen=set()
    def walk(x):
        if x in seen:return
        seen.add(x)
        if not leaf(x):walk(x[0]);walk(x[1])
    walk(t);rr=rows(t)
    return dict(dag_nodes=len(seen),leaf_occurrences=len(rr),maximum_depth=max(len(p)for p,_,_ in rr),maximum_zero_run=max(len(z)for p,_,_ in rr for z in p.split('1')))
def audit(baseline,candidate,read_b_at,common=False):
    raw=Path(baseline).read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
    old=parse(json.loads(raw));expected=construct(old,read_b_at,common)
    actual=parse(json.loads(Path(candidate).read_text()))
    eg=structured_graph(expected);ag=structured_graph(actual)
    assert eg==counter_graph(rows(expected))
    assert ag==counter_graph(rows(actual))
    assert signature(eg)==signature(ag),'changed primitive effect or control target'
    return dict(verified=True,baseline_sha256=hashlib.sha256(raw).hexdigest(),
                candidate_sha256=hashlib.sha256(Path(candidate).read_bytes()).hexdigest(),
                schedule='a194_b194_f1_common'if common else f'a221_b{read_b_at}_f0_s1',input_order='zyx'if common else 'xy'if read_b_at==326 else'yx',
                primitive_cases=len(ag),expected_metrics=metrics(expected),candidate_metrics=metrics(actual),
                scope='Exact primitive word and complete control graph; arithmetic macro contracts are the report dependency.')
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('baseline');ap.add_argument('candidate')
    ap.add_argument('--common',action='store_true')
    ap.add_argument('--read-b-at',type=int,default=194);args=ap.parse_args()
    print(json.dumps(audit(args.baseline,args.candidate,args.read_b_at,args.common),indent=2))
