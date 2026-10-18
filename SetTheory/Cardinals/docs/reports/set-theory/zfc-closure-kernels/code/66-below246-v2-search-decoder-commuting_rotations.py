#!/usr/bin/env python3
"""Finite structural search for association plus disjoint-support commutation."""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict,Counter
from itertools import permutations
import json
import explore as e

@lru_cache(None)
def effects(t):
    if t[0]=='L':
        return (frozenset([t[1][1]])if t[1][0]in('inc','dec')else frozenset(),t[1][0]=='halt')
    a,h=effects(t[1]);b,j=effects(t[2]);return(a|b,h or j)

def main():
    assert __debug__
    qtree={q:e.STATES[q][0]for q in e.PURE if len(e.STATES[q])==1}
    closed={q for q,t in qtree.items()if e.bc(t[1])==e.bc(t[2])==(0,0)}
    pair=defaultdict(list)
    for q in e.PURE:pair[e.T[q,0][2],e.T[q,1][2]].append(q)
    counts=Counter();candidates=[]
    for q in sorted(closed):
        for internalbit in(0,1):
            r=e.T[q,internalbit][2]
            if r not in closed or e.INCOMING[r]!=[(q,internalbit)]:continue
            counts['private_inner_shapes']+=1
            if internalbit==1:
                qs=[e.T[q,0][2],e.T[r,0][2],e.T[r,1][2]]
                ts=[qtree[q][1],qtree[q][2][1],qtree[q][2][2]]
            else:
                qs=[e.T[r,0][2],e.T[r,1][2],e.T[q,1][2]]
                ts=[qtree[q][1][1],qtree[q][1][2],qtree[q][2]]
            ef=list(map(effects,ts))
            for perm in permutations(range(3)):
                if perm==(0,1,2):continue
                counts['nonidentity_permutations_considered']+=1
                valid=True
                for a in range(3):
                    for b in range(a+1,3):
                        if perm.index(a)>perm.index(b)and(ef[a][0]&ef[b][0]or ef[a][1]or ef[b][1]):valid=False
                if not valid:continue
                counts['disjoint_support_permutations']+=1
                a,b,c=[qs[i]for i in perm]
                for side,key in[(0,(a,b)),(1,(b,c))]:
                    for s in pair[key]:
                        if s in(q,r):continue
                        candidates.append(dict(outer=q,removed=r,old_atoms=qs,permutation=perm,
                            inner_side=side,reused=s,supports=[sorted(x[0])for x in ef]))
    result=dict(status='BOUNDED_STRUCTURAL_SEARCH_COMPLETE',source_sequence_states=len(closed),
        reusable_pure_source_states=len(e.PURE),counts=dict(counts),candidates=candidates,
        candidate_count=len(candidates),scope='Both associative shapes, a physically private sequence child, all five nonidentity atom permutations, pair reuse among observed pure source decoder states.',
        commutation_condition='Every inverted pair has disjoint increment/decrement register support and neither subtree contains halt.',
        interpretation='No candidate in this finite family; not a state lower bound or a proof that another encoding cannot improve the table.')
    Path(__file__).with_name('commuting-rotations-result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
