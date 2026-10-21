#!/usr/bin/env python3
"""Independent complete guarded-CFG comparison for the new K215 source.

The arithmetic and subtree-interval constructions are separately implemented.
Equality proves source bisimulation for arbitrary natural-register stores; it
says nothing alone about binary-machine runtime or foundational calibration.
"""
import argparse,hashlib,json,sys
from pathlib import Path


def analyze(rows):
    indices={p:i for i,(p,_,_)in enumerate(rows)};assert len(indices)==len(rows)
    prefixes={p[:i]for p in indices for i in range(len(p))}
    assert not prefixes&set(indices)
    assert all(p+b in prefixes or p+b in indices for p in prefixes for b in'01')
    assert all(p and set(p)<={'0','1'}for p in indices)
    for p,op,r in rows:
        assert op in('CI','CD','CB','CC','CH')
        if op=='CH':assert r is None
        elif op in('CI','CD'):assert type(r)is int and 0<=r<9
        else:assert type(r)is int and r>=1
    intervals={};nodes=set();order=[]
    def visit(p):
        if p in indices:
            i=indices[p];intervals[p]=(i,i+1);order.append(i);node=tuple(rows[i][1:])
        else:
            a,b=visit(p+'0'),visit(p+'1');lo,mid=intervals[p+'0'];mid2,hi=intervals[p+'1'];assert mid==mid2
            intervals[p]=(lo,hi);node=(a,b)
        nodes.add(node);return node
    visit('');assert order==list(range(len(rows)))
    def unwind(p,bit,n):
        while p:
            last,p=p[-1],p[:-1]
            if last==bit:
                n-=1
                if n==0:return intervals[p][1]%len(rows)if bit=='0'else intervals[p][0]
        return 0
    intervals_graph=[]
    for i,(p,op,r)in enumerate(rows):
        after=(i+1)%len(rows)
        if op=='CI':g=(('inc',r),(after,))
        elif op=='CD':g=(('dec',r),(unwind(p,'0',1),after))
        elif op=='CB':g=(('id',),(unwind(p,'0',r),))
        elif op=='CC':g=(('id',),(unwind(p,'1',r),))
        else:g=(('halt',),())
        intervals_graph.append(g)
    depth=max(map(len,indices));checks=0
    def find(p):
        nonlocal checks
        padded=p+'0'*depth
        for n in range(1,depth+1):
            if padded[:n]in indices:
                assert '1'not in p[n:];checks+=1;return indices[padded[:n]]
        raise ValueError(p)
    def plus(p):
        return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')if p else''
    def cut(p,bit,n):
        places=[i for i,x in enumerate(p)if x==bit]
        return p[:places[-n]]if len(places)>=n else''
    arithmetic=[]
    for p,op,r in rows:
        if op=='CI':g=(('inc',r),(find(plus(p)),))
        elif op=='CD':g=(('dec',r),(find(plus(cut(p,'0',1))),find(plus(p))))
        elif op=='CB':g=(('id',),(find(plus(cut(p,'0',r))),))
        elif op=='CC':g=(('id',),(find(cut(p,'1',r)),))
        else:g=(('halt',),())
        arithmetic.append(g)
    assert find('')==0 and arithmetic==intervals_graph
    return arithmetic,{'distinct_DAG_nodes':len(nodes),'leaf_occurrences':len(rows),'maximum_depth':depth,'maximum_zero_run':max(len(z)for p, _, _ in rows for z in p.split('1')),'successor_plus_initial_checks':checks}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in('reference','candidate','output'):ap.add_argument('--'+n,type=Path,required=True)
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
    raw=[args.reference.read_bytes(),args.candidate.read_bytes()];rows=[json.loads(x)for x in raw]
    left,lmetrics=analyze(rows[0]);right,rmetrics=analyze(rows[1]);assert left==right
    assert [r[1:]for r in rows[0]]==[r[1:]for r in rows[1]]
    out={'status':'INDEPENDENT_ALL_NATURAL_SOURCE_BISIMULATION_PASS','reference_sha256':hashlib.sha256(raw[0]).hexdigest(),'candidate_sha256':hashlib.sha256(raw[1]).hexdigest(),
         'literal_primitive_word_equal':True,'complete_guarded_CFG_equal':True,'two_resolvers_agree':True,
         'reference_metrics':lmetrics,'candidate_metrics':rmetrics,'guarded_successors':sum(len(x[1])for x in left),
         'CFG_sha256':hashlib.sha256(json.dumps(left,separators=(',',':')).encode()).hexdigest(),
         'theorem':'For every primitive ordinal and every natural register store, equal effects/guards and equal successor ordinals preserve the identity relation in one source step. Halting is therefore equivalent for all corresponding source configurations.',
         'scope':'Source bisimulation to the credited public Permuted Commands216 source. Its numerical-calculus calibration is inherited; exact binary primitive runtime and blank initialization are separate checks.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
