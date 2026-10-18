#!/usr/bin/env python3
"""Export the exact closed-sequence grammar; this does not certify a rewrite."""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import hashlib, json
import explore as e

bound = lru_cache(None)(e.bc)
qtree = {q:e.STATES[q][0] for q in e.PURE if len(e.STATES[q]) == 1}
seq = {q for q,t in qtree.items() if bound(t[1]) == bound(t[2]) == (0,0)}
roots = {q for q in seq if any(i not in seq for i,b in e.INCOMING[q])} | {96}
atoms = defaultdict(set)
for q in sorted(seq):
    for b in (0,1):
        child = e.T[q,b][2]
        if child not in seq:
            atoms[child].add(qtree[q][b+1])
        else:
            assert qtree[child] == qtree[q][b+1]
variants = {q:sorted(ts,key=repr) for q,ts in atoms.items()}
observed = defaultdict(set)
for q in sorted(seq):
    for b in (0,1):
        child=e.T[q,b][2]
        if child not in seq:
            name=str(child)+':'+str(variants[child].index(qtree[q][b+1]))
            observed[name].add(str(b))

@lru_cache(None)
def flat(q, semantic=False):
    result = ()
    for b in (0,1):
        child = e.T[q,b][2]
        if child in seq:
            result += flat(child,semantic)
        elif semantic:
            result += (str(child)+':'+str(variants[child].index(qtree[q][b+1])),)
        else:
            result += (child,)
    return result

# The DAG is exact and keeps even context-dependent atom trees small.
dag=[]; index={}
def intern(t):
    if t in index:return index[t]
    row = ['L',list(t[1])] if t[0]=='L' else ['N',intern(t[1]),intern(t[2])]
    i=len(dag);dag.append(row);index[t]=i;return i
original = intern(e.ORIGINAL)
projections=[]
def projection(root,known,reason):
    current=root;prefix='';word=None
    for b in known:
        prefix+=str(b)
        child=e.T[current,b][2]
        if child in seq:
            word=flat(child,True);current=child
        else:
            variant=variants[child].index(qtree[current][b+1])
            word=(str(child)+':'+str(variant),)
            break
    return dict(root=root,prefix=prefix,word=word,reason=reason,
        kind='conservative fixed-prefix projection; not a complete context certificate')
for (source,read),(write,direction,target) in sorted(e.T.items()):
    if source in seq or direction!='L' or target not in seq:
        continue
    for previous in(0,1):
        projections.append(projection(target,(previous,write),dict(source=source,read=read,write=write,previous=previous)))
# Two additional lookback entries cross unchanged pure state177 before reaching
# a mutable sequence root, whose next input bit is already fixed.
for source,read in((153,1),(159,0)):
    write,direction,target=e.T[source,read]
    assert direction=='L'and target==177
    for previous in(0,1):
        w,d,next_root=e.T[177,previous]
        assert(w,d)==(previous,'R')and next_root in seq
        projections.append(projection(next_root,(write,),dict(source=source,read=read,write=write,previous=previous,via=177)))
out = dict(
    status='SEARCH_INSTANCE_ONLY',
    table_sha256=hashlib.sha256((e.BASE/'machine/zfc_prefix246_old.tm').read_bytes()).hexdigest(),
    source_sha256=hashlib.sha256((e.BASE/'sources/Prog254.v').read_bytes()).hexdigest(),
    decoder_start=96,
    sequence_states=sorted(seq),
    required_entry_roots=sorted(roots),
    rules={str(q):[e.T[q,b][2] for b in (0,1)] for q in sorted(seq)},
    incoming={str(q):e.INCOMING[q] for q in sorted(seq)},
    flattened_physical_words={str(q):flat(q) for q in sorted(seq)},
    flattened_semantic_words={str(q):flat(q,True) for q in sorted(seq)},
    sequence_ast_roots={str(q):intern(qtree[q]) for q in sorted(seq)},
    atoms={str(q)+':'+str(i):dict(state=q,variant=i,ast=intern(t),bounds=bound(t),leaves=len(e.paths(t)),
               observed_final_incoming_bits=sorted(observed[str(q)+':'+str(i)]),
               rows=[e.T[q,b]for b in(0,1)])
           for q,ts in sorted(variants.items()) for i,t in enumerate(ts)},
    ambiguous_atomic_states=[q for q,ts in sorted(variants.items()) if len(ts)>1],
    left_entry_projection_constraints=projections,
    original_ast=original,
    ast_dag=dag,
    cautions=[
      'Semantic words distinguish atomic contexts; physical words intentionally do not.',
      'The root set is derived from literal physical incoming edges, including non-decoder use.',
      'Pure states are only those reached during the initial unchanged right-moving decoder prefix.',
      'A new grammar must preserve atomic context folds or unfold and re-cost them.',
      'A grammar improvement alone is not a valid TM; new leaf paths, RM bisimulation, whole-frame symbolic replay, and blank bootstrap must all be checked.'
    ])
dest=Path(__file__).with_name('closed-sequence-grammar.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(file=str(dest),sequence_states=len(seq),entry_roots=len(roots),physical_atoms=len(atoms),semantic_atoms=sum(map(len,variants.values())),ast_dag_nodes=len(dag)),indent=2))
