#!/usr/bin/env python3
"""Explore source reassociation with exact control-target repair.

Every retained CI/CD occurrence uses its original register. Every branch must
reach the same next instruction occurrence. CB/CC may be exchanged or have
their strip count changed within the existing operand alphabet. The result
is source-level evidence, not a binary-machine proof.
"""
import json
import time
from bisect import bisect_right
import rotation_search as r

ALPHABET=(('CB',1),('CC',1),('CC',2),('CC',3))

def repair(root,base_leaves,cases,by_leaf,first,alphabet=ALPHABET):
    ls=r.flatten(root)
    assert len(ls)==len(base_leaves)
    depth=max(len(p) for p,op,n in ls)
    starts=[int(p,2)<<(depth-len(p)) for p,_,_ in ls]
    cache={}
    def decode(pc):
        if pc is None:return None
        if pc in cache:return cache[pc]
        x=(int(pc,2) if pc else 0)<<(depth-len(pc))
        i=bisect_right(starts,x)-1
        if i<0 or '1' in pc[len(ls[i][0]):]:i=-1
        cache[pc]=i;return i
    replacement=[];edits=[];ambiguity=[]
    for i,(p,op,n) in enumerate(ls):
        oldp,oldop,oldn,*_=base_leaves[i]
        if oldop not in ('CB','CC'):
            assert (op,n)==(oldop,oldn)
            for c in by_leaf[i]:
                _,positive,target=cases[c]
                if decode(r.successor(p,op,n,positive))!=target:return None
            replacement.append((op,n));continue
        target=cases[by_leaf[i][0]][2]
        choices=[(o,a) for o,a in alphabet if decode(r.successor(p,o,a,None))==target]
        if not choices:return None
        choice=(oldop,oldn) if (oldop,oldn) in choices else choices[0]
        replacement.append(choice)
        if choice!=(oldop,oldn):edits.append([i,oldp,p,[oldop,oldn],list(choice)])
        if len(choices)>1:ambiguity.append([i,choices])
    cursor=0
    def rec(node):
        nonlocal cursor
        e=r.entries[node]
        if e[0]=='N':return r.mk(('N',rec(e[1]),rec(e[2])))
        answer=r.mk(replacement[cursor]);cursor+=1;return answer
    result=rec(root)
    assert cursor==len(ls)
    final=r.flatten(result)
    for c,(i,positive,target) in enumerate(cases):
        p,op,n=final[i]
        assert decode(r.successor(p,op,n,positive))==target,(c,i)
    return result,dict(unique_pairs=len(r.reachable(result)),maximum_depth=depth,
        maximum_zero_run=max(max(map(len,p.split('1'))) for p,_,_ in final),
        edited_control_occurrences=len(edits),edits=edits,
        ambiguous_occurrences=len(ambiguity),exact_all_guard_successors=True,
        original_register_operations_preserved=True,guard_count=len(cases),leaf_count=len(ls))

def main():
    started=time.monotonic();raw=r.a.PROGRAM.read_bytes()
    ls,cases,by,first=r.a.read_program(raw);original=r.load(raw)
    base=r.rotate(original,95,'left');seen=set();records=[];saved=[];admitted=0
    for name,start in [('original',original),('rotation202',base)]:
        for p in r.reachable(start):
            for direction in ('left','right'):
                candidate=r.rotate(start,p,direction)
                if candidate is None or candidate in seen:continue
                seen.add(candidate)
                outcome=repair(candidate,ls,cases,by,first)
                if outcome is None:continue
                admitted+=1;result,meta=outcome
                meta.update(origin=name,pivot=p,direction=direction)
                records.append({k:v for k,v in meta.items() if k!='edits'})
                if meta['unique_pairs']<202 or meta['maximum_zero_run']<7 or meta['edited_control_occurrences'] and meta['unique_pairs']<=202:
                    path=r.OUT/f'rotation_control_candidate_{len(saved):03}.json'
                    r.dump_graph(result,path,meta);saved.append(str(path))
                    print(json.dumps({k:v for k,v in meta.items() if k!='edits'}),flush=True)
    out=dict(tested=len(seen),admitted=admitted,seconds=time.monotonic()-started,
        alphabet=ALPHABET,saved=saved,records=records)
    (r.OUT/'rotation_control_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2),flush=True)

if __name__=='__main__':main()
