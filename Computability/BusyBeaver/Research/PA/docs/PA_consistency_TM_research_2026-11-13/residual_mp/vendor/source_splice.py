#!/usr/bin/env python3
"""Reproduce the storage-free dominated-rho8 source from accepted K219.

Python 3 standard library only. The default source has MP-only additive
input, YX field order, and 205 DAG nodes. --common preserves the original
common input and all non-AX branches, producing the 206-node ZYX reference
source. Its default after_u schedule is a194_b194_f1; --common-schedule
before_u reproduces a194_b161_f0. Optional --equivalent proves that a later
source has exactly the same guarded ordinal CFG. For the common variant
it additionally checks literal preservation of every primitive path
outside the original AX subtree.

The mathematical calibration is in dominated_command_calibration.tex and
dominated_common_input_calibration.tex. This is a source checker, not a
binary-machine runtime or initialization checker.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse,json,hashlib

def leaf(t):return isinstance(t[0],str)
def parse(rows):
    dd={p:(o,r)for p,o,r in rows}
    assert len(dd)==len(rows)
    def go(p=''):
        if p in dd:return dd[p]
        return go(p+'0'),go(p+'1')
    tree=go();assert [list(x)for x in sites(tree)]==rows
    return tree

def sites(t,p=''):
    return [(p,*t)]if leaf(t)else sites(t[0],p+'0')+sites(t[1],p+'1')

@lru_cache(None)
def size(t):return 1 if leaf(t)else size(t[0])+size(t[1])

@lru_cache(None)
def boundary(t):
    if leaf(t):
        o,r=t
        if o=='CD':return 1,0,False
        if o=='CB':return r,0,False
        if o=='CC':return 0,r,False
        if o=='CH':return 0,0,True
        assert o=='CI';return 0,0,False
    a,b=map(boundary,t)
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]

def nodes(t):
    seen=set()
    def go(q):
        if q in seen:return
        seen.add(q)
        if not leaf(q):go(q[0]);go(q[1])
    go(t);return seen

def metrics(t):
    ss=sites(t)
    return dict(dag_nodes=len(nodes(t)),leaf_occurrences=len(ss),maximum_depth=max(len(p)for p,_,_ in ss),maximum_zero_run=max(len(z)for p,_,_ in ss for z in p.split('1')))

def serial(xs):
    assert xs
    return xs[0]if len(xs)==1 else(xs[0],serial(xs[1:]))

def closed_forest(t,lo,hi):
    out=[]
    def go(q,i=0):
        j=i+size(q)
        if j<=lo or hi<=i:return
        if lo<=i and j<=hi:
            assert boundary(q)==(0,0,False),(i,j,boundary(q))
            out.append(q);return
        assert not leaf(q)
        go(q[0],i);go(q[1],i+size(q[0]))
    go(t);assert sum(map(size,out))==hi-lo
    return out

def apply_closed_splices(t,edits):
    used=Counter()
    def go(q,i=0):
        j=i+size(q)
        overlap=[(rg,new)for rg,new in edits.items()if not(j<=rg[0]or rg[1]<=i)]
        if not overlap:return q
        for(lo,hi),new in overlap:
            if lo<=i and j<=hi:
                assert boundary(q)==(0,0,False),(i,j,boundary(q))
                if i==lo:used[lo,hi]+=1;return new
                return None
        assert not leaf(q)
        a=go(q[0],i);b=go(q[1],i+size(q[0]))
        if a is None and b is not None:
            assert boundary(b)[:2]==(0,0), ('open right remainder',i,j,boundary(b))
            return b
        if b is None and a is not None:
            assert boundary(a)[:2]==(0,0), ('open left remainder',i,j,boundary(a))
            return a
        return None if a is None else(a,b)
    result=go(t)
    assert used==Counter({rg:1 for rg in edits})
    return result

def cfg_intervals(rows):
    ranges={}
    for i,(p,o,r)in enumerate(rows):
        for k in range(len(p)+1):
            q=p[:k]
            if q not in ranges:ranges[q]=[i,i+1]
            else:ranges[q][1]=i+1
    def target(p,bit,n):
        for j in range(len(p)-1,-1,-1):
            if p[j]==bit:
                n-=1
                if n==0:return ranges[p[:j]][int(bit=='0')]%len(rows)
        return 0
    out=[]
    for i,(p,o,r)in enumerate(rows):
        if o=='CI':dest=((i+1)%len(rows),)
        elif o=='CD':dest=(target(p,'0',1),(i+1)%len(rows))
        elif o=='CB':dest=(target(p,'0',r),)
        elif o=='CC':dest=(target(p,'1',r),)
        else:assert o=='CH';dest=()
        out.append((o,r if o in('CI','CD')else None,dest))
    return out

def cfg_arithmetic(rows):
    lookup={p:i for i,(p,o,r)in enumerate(rows)};depth=max(map(len,lookup))
    def direct(p):
        q=p+'0'*(depth+1)
        for k in range(1,len(q)+1):
            if q[:k]in lookup:
                assert '1'not in p[k:];return lookup[q[:k]]
        raise AssertionError(p)
    def inc(p):return format((int(p,2)+1)%2**len(p),f'0{len(p)}b')if p else''
    def cut(p,bit,n):
        js=[j for j,b in enumerate(p)if b==bit]
        return p[:js[-n]]if len(js)>=n else''
    out=[]
    for p,o,r in rows:
        if o=='CI':dest=(direct(inc(p)),)
        elif o=='CD':dest=(direct(inc(cut(p,'0',1))),direct(inc(p)))
        elif o=='CB':dest=(direct(inc(cut(p,'0',r))),)
        elif o=='CC':dest=(direct(cut(p,'1',r)),)
        else:assert o=='CH';dest=()
        out.append((o,r if o in('CI','CD')else None,dest))
    return out

def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode()
def sha(x):return hashlib.sha256(x).hexdigest()

def build(t,common=False,common_schedule="after_u"):
    assert metrics(t)==dict(dag_nodes=206,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6)
    get=lambda lo,hi:serial(closed_forest(t,lo,hi))
    a=get(40,66);read_a=get(23,37);read_b=get(121,135);imp=get(194,221)
    assert common_schedule in ('before_u','after_u')
    common_edits=({(121,135):None,(161,194):(read_b,a),(194,221):(read_a,imp)}if common_schedule=='before_u'else
                  {(121,135):None,(161,194):a,(194,221):(read_b,(read_a,imp))})
    edits=(common_edits if common else
           {(23,37):None,(121,135):None,(161,194):a,(194,221):(read_b,imp),(221,247):(read_a,a),(4652,4678):(read_a,a)})
    result=apply_closed_splices(t,edits)
    expected=(dict(dag_nodes=206,leaf_occurrences=4751,maximum_depth=38,maximum_zero_run=8)if common else
              dict(dag_nodes=205,leaf_occurrences=4751,maximum_depth=37,maximum_zero_run=8))
    assert metrics(result)==expected
    return result,edits

def main():
    ap=argparse.ArgumentParser();ap.add_argument('baseline',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--equivalent',type=Path);ap.add_argument('--common',action='store_true',help='Retain original common input and all non-AX branches');ap.add_argument('--common-schedule',choices=['before_u','after_u'],default='after_u',help='Place cached-parameter read before or after loading U; only with --common');a=ap.parse_args()
    raw=a.baseline.read_bytes();old=parse(json.loads(raw));new,edits=build(old,a.common,a.common_schedule);rr=sites(new)
    graph=cfg_intervals(rr);assert graph==cfg_arithmetic(rr)
    a.output.mkdir(parents=True,exist_ok=True);source=compact(rr);(a.output/('dominated_zyx206.json'if a.common else'dominated_yx205.json')).write_bytes(source)
    receipt=dict(status='EXACT_SOURCE_CONSTRUCTION_AND_CONTROL_FLOW_CHECK',baseline_sha256=sha(raw),source_sha256=sha(source),metrics=metrics(new),input_order='zyx'if a.common else'yx',edits=[list(rg)for rg in edits],cfg_sha256=sha(compact(graph)),axiom_semantics=('GEN(U,H); rho8(A,B,C,U), U=oldD+z, A=U+x, B=oldH+y; original common input and all non-AX branches retained'if a.common else'GEN(U,H); rho8(A,B,C,U), U=oldD, A=U+x, B=oldH+y; only MP has a non-AX additive field'))
    if a.common:
        ax_prefix='11101001001';oldmap={p:(o,r)for p,o,r in sites(old)};newmap={p:(o,r)for p,o,r in rr}
        outside={p:v for p,v in oldmap.items()if not p.startswith(ax_prefix)}
        assert all(newmap.get(p)==v for p,v in outside.items())
        receipt['common_schedule']=a.common_schedule
        receipt['outside_ax_preservation']=dict(ax_subtree_prefix=ax_prefix,primitive_leaves=len(outside),exact_opcodes_and_operands=True)
    if a.equivalent:
        targetraw=a.equivalent.read_bytes();targetrows=json.loads(targetraw);target=parse(targetrows)
        g2=cfg_intervals(targetrows);assert g2==cfg_arithmetic(targetrows)
        assert g2==graph,'Candidate does not preserve the exact guarded ordinal CFG'
        if a.common:
            targetmap={p:(o,r)for p,o,r in targetrows}
            assert all(targetmap.get(p)==v for p,v in outside.items()),'Candidate changed a protected source path outside AX'
        receipt['equivalent_source']=dict(sha256=sha(targetraw),metrics=metrics(target),guarded_cases=sum(2 if o=='CD'else 1 for p,o,r in targetrows))
    (a.output/'source_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
