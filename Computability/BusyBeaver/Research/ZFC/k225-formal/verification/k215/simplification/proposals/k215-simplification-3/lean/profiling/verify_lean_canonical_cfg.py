#!/usr/bin/env python3
"""Independent canonical CFG audit of the pinned literal Lean decoder trees.
No Lean/Rocq compiler result is implied. Uses profile_forward_checks.py's
strict parser and path arithmetic, not Rocq CFG output. Rejects Python -O.
"""
from __future__ import annotations
import collections, contextlib, io, json, runpy, sys
from pathlib import Path
if not __debug__: raise SystemExit('Do not run with -O/-OO: assertions are required.')
ROOT=Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):
    p=runpy.run_path(str(ROOT/'profile_forward_checks.py'))
nodes=p['nodes']; roots=(p['source'],p['target']); entries=p['entries']
inc,brk,cont=p['inc'],p['brk'],p['cont']

def leaves(t,path=()):
    if nodes[t][0]=='leaf': return [(path,nodes[t][1:])]
    return leaves(nodes[t][1],path+(0,))+leaves(nodes[t][2],path+(1,))

def site(t,path):
    d=0
    while nodes[t][0]=='node':
        b=path[d] if d<len(path) else 0
        t=nodes[t][1+b];d+=1
    return nodes[t][1:],(path+(0,)*d)[:d]

def successors(edge,q):
    kind,arg=edge
    if kind=='halt':return ()
    if kind=='inc':return (inc(q),)
    if kind=='decnz':return (inc(q),brk(q,1))
    if kind=='brk':return (brk(q,arg),)
    if kind=='cont':return (cont(q,arg),)
    raise AssertionError(kind)

def compile_cfg(root):
    ls=leaves(root)
    prim=[(q,e) for q,e in ls if e[0] not in ('brk','cont')]
    tests=[(q,e) for q,e in ls if e[0] in ('decnz','halt')]
    pi={q:i for i,(q,e) in enumerate(prim)}
    ti={q:i for i,(q,e) in enumerate(tests)}
    ctrl_max=0; block_max=0
    def resolve(path,block=False):
        nonlocal ctrl_max,block_max
        seen=set(); counts=collections.Counter();steps=0
        while True:
            edge,q=site(root,path)
            assert q not in seen, 'Control/increment-only cycle: cannot silently contract'
            seen.add(q);steps+=1
            if edge[0] in ('decnz','halt') if block else edge[0] not in ('brk','cont'):
                if block:block_max=max(block_max,steps)
                else:ctrl_max=max(ctrl_max,steps-1)
                return ((ti if block else pi)[q],tuple(sorted(counts.items())))
            if edge[0]=='inc':counts[edge[1]]+=1
            ss=successors(edge,q);assert len(ss)==1
            path=ss[0]
    primitive=[(e,tuple(resolve(r)[0] for r in successors(e,q))) for q,e in prim]
    block=[(e,tuple(resolve(r,True) for r in successors(e,q))) for q,e in tests]
    start_primitive=resolve(())[0];start_block=resolve((),True)
    return dict(leaves=ls,primitive=primitive,block=block,ti=ti,pi=pi,
        start_primitive=start_primitive,start_block=start_block,
        max_control_chain=ctrl_max,max_block_site_visits=block_max)

A,B=map(compile_cfg,roots)
assert len(A['leaves'])==len(B['leaves'])==4751
assert len(A['primitive'])==len(B['primitive'])==3326
assert len(A['block'])==len(B['block'])==1426
assert A['start_primitive']==B['start_primitive']==0
assert A['start_block']==B['start_block']
assert [e[0] for e,s in A['primitive']]==[e[0] for e,s in B['primitive']]
assert [s for e,s in A['primitive']]==[s for e,s in B['primitive']]
assert A['block']==B['block'], 'Register-count block CFG differs'
mismatch=[i for i,(a,b) in enumerate(zip(A['primitive'],B['primitive'])) if a!=b]
assert len(mismatch)==512
pairs=[];schemas=collections.Counter();pred=collections.defaultdict(list)
for i,(_,ss) in enumerate(A['primitive']):
    for j in ss:pred[j].append(i)
for i in range(0,len(mismatch),2):
    a,b=mismatch[i:i+2];assert b==a+1
    ae,ass=A['primitive'][a];be,bss=A['primitive'][b]
    ce,css=B['primitive'][a];de,dss=B['primitive'][b]
    assert ae[0]==be[0]==ce[0]==de[0]=='inc'
    assert ae==de and be==ce and ae!=be
    assert ass==css==(b,) and bss==dss and pred[b]==[a]
    assert b!=A['start_primitive']
    pairs.append((a,b));schemas[(ae[1],be[1],ce[1],de[1])]+=1
assert len(pairs)==256
canonical=[]
for a,b,z,u,v in entries:
    ea,qa=site(roots[0],p['decode_raw'](a))
    eb,qb=site(roots[1],p['decode_raw'](b))
    ia,ib=A['ti'][qa],B['ti'][qb]
    assert ea==eb and ia==ib and z==0
    canonical.append((ia,ib))
assert len(set(canonical))==1426
out={
 'status':'PASS_PYTHON_CANONICAL_LEAN_CFG_NOT_KERNEL_CHECKED',
 'commit':p['out']['commit'],'source_sha256':p['out']['source_sha256'],
 'expanded_leaves_per_tree':4751,'primitive_ordinals_per_tree':3326,
 'all_successor_ordinals_equal':True,'all_primitive_kinds_equal':True,
 'increment_label_mismatch_ordinals':len(mismatch),'adjacent_independent_swap_pairs':len(pairs),
 'swap_schemas':[{'p215':[a,b],'dagPerm':[c,d],'occurrences':n} for (a,b,c,d),n in schemas.items()],
 'block_cfg_equal_including_initial':True,'block_test_halt_rows':1426,
 'block_branches_including_initial':2851,
 'certificate_raw_entries':len(entries),'certificate_unique_canonical_pairs':len(set(canonical)),
 'certificate_alias_entries':len(entries)-len(set(canonical)),
 'max_control_only_chain_per_program':[A['max_control_chain'],B['max_control_chain']],
 'max_block_site_visits_per_program':[A['max_block_site_visits'],B['max_block_site_visits']],
 'all_swap_interiors_have_unique_predecessor':True,
 'limitations':['Data equality, not a soundness proof for CFG extraction.',
   'Does not prove exact structured dagPerm nodes188/190: that separate provenance audit is in rocq/.',
   'Reuses the strict Lean-tree parser/path arithmetic, not external Rocq CFG files.']
}
(ROOT/'canonical_cfg_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
