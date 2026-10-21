#!/usr/bin/env python3
"""Exact deterministic labeled-bisimulation minimization of both Lean CFGs.
Reads only packaged local pinned Lean data through the parent strict parser.
Not a Lean kernel proof. No timing/speedup claim. Rejects optimized Python.
"""
from __future__ import annotations
import collections, contextlib, copy, hashlib, io, json, runpy, sys
from pathlib import Path
if not __debug__: raise SystemExit('Do not run with -O/-OO: assertions are required.')
ROOT=Path(__file__).resolve().parent
with contextlib.redirect_stdout(io.StringIO()):
    m=runpy.run_path(str(ROOT.parent/'verify_lean_canonical_cfg.py'))

def partition(keys):
    ids={};out=[]
    for key in keys:
        if key not in ids:ids[key]=len(ids)
        out.append(ids[key])
    return out

def minimize(graph,start):
    n=len(graph)
    # Node labels preserve halt versus exact tested register. Branch position
    # is part of the tuple: positive precedes zero, never reordered.
    classes=partition([row[0] for row in graph]);rounds=[len(set(classes))]
    while True:
        keys=[(edge,tuple((counts,classes[j]) for j,counts in outgoing))
              for edge,outgoing in graph]
        refined=partition(keys);rounds.append(len(set(refined)))
        # Starting from node labels, refinement cannot merge old classes.
        assert all(classes[i]==classes[j] for ids in
            ([i for i,c in enumerate(refined) if c==k] for k in set(refined))
            for i,j in zip(ids,ids[1:]))
        if refined==classes:break
        classes=refined
    members=collections.defaultdict(list)
    for i,c in enumerate(classes):members[c].append(i)
    quotient=[]
    for c in range(len(members)):
        sig=keys[members[c][0]]
        assert all(keys[i]==sig for i in members[c])
        quotient.append(sig)
    # Verify the quotient is stable and itself has no further bisimilar nodes.
    qclasses=partition([x[0] for x in quotient])
    while True:
        qnext=partition([(e,tuple((cs,qclasses[j]) for cs,j in out)) for e,out in quotient])
        if qnext==qclasses:break
        qclasses=qnext
    assert len(set(qclasses))==len(quotient)
    initial=(classes[start[0]],start[1])
    reach={start[0]};todo=[start[0]]
    while todo:
        i=todo.pop()
        for j,_ in graph[i][1]:
            if j not in reach:reach.add(j);todo.append(j)
    return dict(classes=classes,members=dict(members),quotient=quotient,
        initial=initial,round_class_counts=rounds,reachable_original_nodes=len(reach))

A=minimize(m['A']['block'],m['A']['start_block'])
B=minimize(m['B']['block'],m['B']['start_block'])
assert A==B
def check_quotient(graph,start,receipt):
    cls,quot=receipt['classes'],receipt['quotient']
    assert len(cls)==len(graph) and set(cls)==set(range(len(quot)))
    assert receipt['initial']==(cls[start[0]],start[1])
    for i,(edge,out) in enumerate(graph):
        assert quot[cls[i]]==(edge,tuple((counts,cls[j]) for j,counts in out))
check_quotient(m['A']['block'],m['A']['start_block'],A)
check_quotient(m['B']['block'],m['B']['start_block'],B)
negative=[]
for mode in ('wrong_initial','wrong_class','wrong_count','reversed_branches'):
    bad=copy.deepcopy(A)
    if mode=='wrong_initial':bad['initial']=(1,bad['initial'][1])
    elif mode=='wrong_class':bad['classes'][0]=1
    elif mode=='wrong_count':
        e,outs=bad['quotient'][0];(counts,j),*rest=outs
        bad['quotient'][0]=(e,((counts+((99,1),),j),*rest))
    else:
        k=next(i for i,(_,out) in enumerate(bad['quotient']) if len(out)==2 and out[0]!=out[1])
        e,outs=bad['quotient'][k];bad['quotient'][k]=(e,outs[::-1])
    try:check_quotient(m['A']['block'],m['A']['start_block'],bad)
    except AssertionError:negative.append(mode)
    else:raise AssertionError('Malformed quotient accepted: '+mode)
hist=collections.Counter(map(len,A['members'].values()))
result={
 'status':'PASS_EXACT_PYTHON_LABELED_BISIMULATION_MINIMIZATION_NOT_KERNEL_PROOF',
 'commit':m['out']['commit'],'source_sha256':m['out']['source_sha256'],
 'independent_per_program_results_equal':True,'original_nodes':1426,
 'minimal_classes':len(A['quotient']),'nodes_removed':1426-len(A['quotient']),
 'class_size_histogram':dict(sorted(hist.items())),
 'round_class_counts':A['round_class_counts'],
 'reachable_original_nodes':A['reachable_original_nodes'],
 'initial_edge':A['initial'],
 'maximum_class_size':max(hist),
 'refinement_rounds_including_stability':len(A['round_class_counts'])-1,
 'merged_classes':[{'class':k,'members':v,'row':A['quotient'][k]} for k,v in A['members'].items() if len(v)>1],
 'negative_controls_rejected':negative,
 'semantics':'Exact tested-register/halt node labels; exact increment count vectors; positive/zero branch order preserved.',
 'minimality_scope':'Coarsest exact labeled bisimulation on this finite count-block graph, not all program equivalence or TM state minimization.'
}
(ROOT/'minimization_result.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'quotient_certificate.json').write_text(json.dumps({
 'source_sha256':m['out']['source_sha256'],
 'ordinal_to_class':A['classes'],'class_members':A['members'],
 'quotient_rows':A['quotient'],'initial_edge':A['initial']},separators=(',',':'))+'\n')
print(json.dumps(result,indent=2))
