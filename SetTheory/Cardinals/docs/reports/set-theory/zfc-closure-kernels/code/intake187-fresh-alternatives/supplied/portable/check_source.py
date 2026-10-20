#!/usr/bin/env python3
"""Independent whole-source, exact ordinal CFG and all-natural guard proofs."""
from pathlib import Path
import argparse, hashlib, json, sys
from construct import sha,dump,retag_source,ROOT
def compile_cfg(sites):
    """Resolve control by ancestor walking and leftmost subtree entry.

    On a break, leave the matching ancestor reached through a left edge.
    On a continue, reenter the matching ancestor reached through a right
    edge. The top-level source repeats at its boundary.
    """
    leaves={p:i for i,(p,_,_) in enumerate(sites)}
    assert len(leaves)==len(sites)
    nodes={p[:i] for p in leaves for i in range(len(p))}
    assert not set(leaves)&nodes
    assert all(p+c in nodes or p+c in leaves for p in nodes for c in '01')
    def enter(p):
        while p not in leaves: p+='0'
        return leaves[p]
    def after(p):
        while p and p[-1]=='1': p=p[:-1]
        return enter(p[:-1]+'1') if p else 0
    def control(p,edge,n):
        while p:
            last=p[-1];p=p[:-1]
            if last==edge:
                n-=1
                if n==0:return after(p) if edge=='0' else enter(p)
        return 0
    graph=[]
    for p,op,arg in sites:
        if op=='CH': graph.append([])
        elif op=='CI': graph.append([after(p)])
        elif op=='CD': graph.append([control(p,'0',1),after(p)])
        elif op=='CB': graph.append([control(p,'0',arg)])
        elif op=='CC': graph.append([control(p,'1',arg)])
        else: raise AssertionError(op)
    return graph


def arithmetic_cfg(sites):
    leaves={p:i for i,(p,op,a) in enumerate(sites)}
    maxdepth=max(map(len,leaves));lookups=0
    def locate(address):
        nonlocal lookups
        padded=address+'0'*maxdepth
        for n in range(1,maxdepth+1):
            if padded[:n] in leaves:
                assert '1' not in address[n:],('Stray suffix',address,padded[:n])
                lookups+=1
                return leaves[padded[:n]]
        raise AssertionError(('No leaf for address',address))
    def inc(p):return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b') if p else ''
    def cut(p,b,n):
        indices=[i for i,c in enumerate(p) if c==b]
        return p[:indices[-n]] if len(indices)>=n else ''
    out=[]
    for p,op,a in sites:
        if op=='CI':targets=[inc(p)]
        elif op=='CD':targets=[inc(cut(p,'0',1)),inc(p)]
        elif op=='CB':targets=[inc(cut(p,'0',a))]
        elif op=='CC':targets=[cut(p,'1',a)]
        elif op=='CH':targets=[]
        else:raise AssertionError(op)
        out.append([locate(t) for t in targets])
    assert locate('')==0
    return out,lookups


def prove(old,new,name):
    assert len(old)==len(new)==4744
    a=compile_cfg(old);b=compile_cfg(new)
    for rows,cfg in [(old,a),(new,b)]:
        arithmetic,lookups=arithmetic_cfg(rows)
        assert arithmetic==cfg
    zero=name in ('zero_terminal','composed');retag=name in ('retagged','composed')
    middle=[list(s) for s in new]
    changed_zero=[];changed_control=[];address_changes=0
    for i,(x,y) in enumerate(zip(old,new)):
        address_changes+=x[0]!=y[0]
        if x[1:]!=y[1:]:
            if x[1:]==['CB',1] and y[1:]==['CD',6]:
                assert zero;middle[i][1:]=['CB',1]
                changed_zero.append(i)
            else:
                assert retag and x[1:]==['CC',2] and y[1:]==['CC',3]
                changed_control.append(i)
    assert len(changed_control)==(81 if retag else 0)
    assert len(changed_zero)==(8 if zero else 0)
    # Both implementations compute the exact CFG independently from full syntax.
    # Retagging is identity on the complete primitive step relation by ordinal.
    middle_cfg=compile_cfg(middle)
    assert middle_cfg==a
    assert arithmetic_cfg(middle)[0]==a
    assert all(x[1:]==y[1:] or x[1:]==['CC',2] and y[1:]==['CC',3]
               for x,y in zip(old,middle))
    guards=[]
    for i,(edges,newedges) in enumerate(zip(middle_cfg,b)):
        if i not in changed_zero:
            assert edges==newedges
        else:
            assert edges==[newedges[0]] and i!=0
            incoming=[(j,k) for j,e in enumerate(b) for k,t in enumerate(e) if t==i]
            assert incoming==[(i-2,0)] and new[i-2][1:]==['CD',6]
            guards.append(dict(ordinal=i,predecessor=i-2,guard='R6=0',successor=newedges[0]))
    assert changed_zero==([4570,4576,4588,4594,4602,4608,4711,4717] if zero else [])
    # Recover every subtree to reject missing, duplicate, prefix or malformed leaves.
    def tree(rows):
        d={p:(op,arg) for p,op,arg in rows}
        inside={p[:i] for p in d for i in range(len(p))}
        for p in sorted(inside,key=len,reverse=True): d[p]=(d[p+'0'],d[p+'1'])
        return d
    oldtree,newtree=tree(old),tree(new)
    assert sorted(p for p,x in newtree.items() if isinstance(x[0],str))==[s[0] for s in new]
    # Direct contextual identity U=((D6,C2),B1) == V=((D6,C2),D6),
    # for every natural R6: positive returns continue1 before the last child;
    # zero returns break1 without any register change.
    macros=[]
    if zero:
        before=tree(middle);D5=('CD',5);D6=('CD',6);P=(D6,('CC',2));Z=(D5,('CC',1))
        U=(P,('CB',1));V=(P,D6);E=(((D5,U),D6),(Z,U));F=(((D5,V),D6),(Z,V))
        macros=[p for p,t in before.items() if t==E]
        assert len(macros)==4 and all(newtree[p]==F for p in macros)
    return dict(status='ALL_NATURAL_COMPLETE_SOURCE_EQUIVALENCE_PASS',variant=name,
        leaf_occurrences=len(new),changed_continuations=changed_control,changed_terminals=guards,
        path_changes=address_changes,source_cfg_nodes=len(a),exact_retag_ordinal_cfg=True,
        arithmetic_ancestor_cfg_agreement=True,no_stray_successor_checks=arithmetic_cfg(new)[1],
        generic_cases_expected=sum(2 if op=='CD' else 1 for p,op,arg in new),generic_cases_excluded=0,
        equality_macro_paths=macros,distinct_dag_nodes=len(set(newtree.values())),
        argument='Retagging preserves every register operation and every guarded successor by leaf ordinal; all-natural source traces are in lockstep. At each changed terminal the unique incoming edge is the zero edge of the unchanged D6 two ordinals earlier. Consequently R6=0 at entry; the new failed decrement and old break are identical, including successor. This source invariant is never used to exclude generic runtime cases. Both contextual macro and direct guard checks hold. Halting and divergence are preserved from source entry for every natural register vector.')

if __name__=='__main__':
    assert __debug__ and not sys.flags.optimize
    ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--variant',choices=['zero_terminal','retagged','composed'],required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    cfg=json.loads((ROOT/'machine/construction.json').read_text())
    old=a.baseline/'machine/sites219.json'
    assert sha(old)==cfg['upstream_source_sha256'] and sha(a.source)==cfg['variants'][a.variant]['source_sha256']
    result=prove(json.loads(old.read_text()),json.loads(a.source.read_text()),a.variant)
    result.update(old_source_sha256=sha(old),source_sha256=sha(a.source))
    dump(a.output,result);print(result['status'])
