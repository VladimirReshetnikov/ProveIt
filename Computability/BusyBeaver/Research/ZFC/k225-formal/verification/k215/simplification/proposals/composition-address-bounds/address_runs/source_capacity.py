#!/usr/bin/env python3
"""Exact run-length feasibility under arbitrary closed-fragment reassociation.

A source node may be associated (A;(B;C)) <-> ((A;B);C) iff A,B,C
have boundary (0,0,False). These rotations can be performed at any occurrence.
This DP decides feasibility of maximum zero-run <= Z in the full (unbounded)
associativity closure, not merely in a finite rotation beam.
"""
import json,sys,hashlib,argparse
from functools import cache
from pathlib import Path
import source_language as s
HERE=Path(__file__).resolve().parent
sys.setrecursionlimit(12000)
N=[];lookup={}
def intern(t):
    if t not in lookup:lookup[t]=len(N);N.append(t)
    return lookup[t]
def encode(t):return intern(t if s.leaf(t) else (encode(t[0]),encode(t[1])))
def leaf(n):return isinstance(N[n][0],str)
@cache
def decode(n):return N[n] if leaf(n) else tuple(decode(k) for k in N[n])
@cache
def boundary(n):
    if leaf(n):
        op,a=N[n]
        return (1,0,False) if op=='CD' else (a,0,False) if op=='CB' else (0,a,False) if op=='CC' else (0,0,op=='CH')
    a,b=map(boundary,N[n]);return max(a[0]-1,0,b[0]),max(a[1],b[1]-1,0),a[2] or b[2]
def closed(n):return boundary(n)==(0,0,False)
def free(n):return not leaf(n) and all(closed(c) for c in N[n])
@cache
def factors(n):
    if free(n):return factors(N[n][0])+factors(N[n][1])
    return (n,)

def solve(root,Z):
    tables={};caps={}
    def cap(n):
        if n in caps:return caps[n]
        if leaf(n):v=Z
        elif free(n):
            aa=factors(n);cc=[cap(k) for k in aa];slacks=[];total=0
            for c in cc[:-1]:total+=c;slacks.append(total-len(slacks)-1)
            v=max(-1,min(slacks)) if all(c>=0 for c in cc) else -1
            tables[n]={'factors':aa,'factor_capacities':cc,'prefix_slacks':slacks}
        else:
            l,r=N[n];cl,cr=cap(l),cap(r);v=cl-1 if cl>=1 and cr>=0 else -1
        caps[n]=v;return v
    result=cap(root)
    @cache
    def build(n,r):
        assert cap(n)>=r
        if leaf(n):return n
        l,right=N[n]
        if cap(l)>=r+1 and cap(right)>=0:
            return intern((build(l,r+1),build(right,0)))
        assert free(n)
        aa=factors(n);K=len(aa);cc=[cap(k) for k in aa]
        Q=[0]
        for c in cc:Q.append(Q[-1]+c-1)
        @cache
        def icap(i,j):
            return cc[i] if j==i+1 else min(Q[i+1:j])-Q[i]
        originals={}
        def scan(t,i):
            if not free(t):return i+1
            l,rr=N[t];k=scan(l,i);j=scan(rr,k);originals[i,j]=(t,k);return j
        assert scan(n,0)==K
        def group(i,j,r):
            assert icap(i,j)>=r
            if j==i+1:return build(aa[i],r)
            old,pivot=originals.get((i,j),(None,(i+j)//2))
            candidates=sorted(range(i+1,j),key=lambda k:(k!=pivot,(i,k)not in originals,(k,j)not in originals,abs(2*k-i-j),k))
            for k in candidates:
                if icap(i,k)>=r+1 and icap(k,j)>=0:
                    return intern((group(i,k,r+1),group(k,j,0)))
            assert False
        return group(0,K,r)
    built=build(root,0) if result>=0 else None
    return result,built,caps,tables

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=HERE/'baseline_sites215.json');ap.add_argument('--output',type=Path,default=HERE/'evidence/closed-capacity-result.json');a=ap.parse_args()
    rows=json.loads(a.source.read_text());root=encode(s.tree(rows));original_nodes=len(N);graph=s.graph_intervals(rows);assert graph==s.graph_arithmetic(rows)[0]
    out={'source_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),'original_metrics':s.metrics(decode(root)),'rotation_grammar':'At every occurrence: (A,(B,C)) <-> ((A,B),C), with boundary(A)=boundary(B)=boundary(C)=(0,0,False)','runs':[]}
    for Z in range(1,7):
        c,t,caps,tables=solve(root,Z)
        r={'zero_bound':Z,'root_capacity':c,'feasible':c>=0,'node_capacities':{str(k):v for k,v in sorted(caps.items())},'interval_tables':{str(k):v for k,v in sorted(tables.items())}}
        if c>=0:
            rr=s.sites(decode(t));assert [r[1:]for r in rows]==[r[1:]for r in rr]
            assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]==graph
            metrics=s.metrics(decode(t));assert metrics['maximum_zero_run']<=Z
            name=f'closed-zero-bound-{Z}.json';raw=s.compact(rr);(a.output.parent/name).write_bytes(raw)
            r.update(source_file=name,sha256=hashlib.sha256(raw).hexdigest(),metrics=metrics)
        out['runs'].append(r)
        print({k:v for k,v in r.items()if k not in ('node_capacities','interval_tables')},flush=True)
    out['original_interned_nodes']=[list(n)for n in N[:original_nodes]];out['root_node']=root
    a.output.write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
