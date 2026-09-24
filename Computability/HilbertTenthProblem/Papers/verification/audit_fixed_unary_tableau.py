#!/usr/bin/env python3
"""Independent fixed-unary audit on noncanonical cyclic quotients."""
from pathlib import Path
import hashlib
import json
import sys

import explore_fixed_unary_tableau as candidate

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).with_suffix('.json')


def verify():
    paths=[ROOT/'Papers'/'1980'/'EXPLORATION_FIXED_UNARY_TABLEAU.md',
           ROOT/'Papers'/'verification'/'explore_fixed_unary_tableau.py',
           ROOT/'Papers'/'verification'/'explore_fixed_unary_tableau.json']
    digest=lambda: {path.relative_to(ROOT).as_posix():hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in paths}
    before=digest();cases=cells=0;records=[]
    for modulus,residue in ((1,0),(2,0),(3,1),(5,2)):
        machine=candidate.residue_machine(modulus,residue)
        S,E=candidate.fixed_markers(machine);pred=candidate.predicate(machine)
        for t in range(3,10):
            history=candidate.history_for(machine,t,limit=20)
            if history[-1][2]!=machine.halt:continue
            wmin,hmin=candidate.thresholds(history,t)
            for factor in (2,3):
                H=max(hmin,t+1,wmin)
                h=factor*H;W=h+1;N=W*H
                assert N!=h*(h+1) and h*t<N
                grid=candidate.build_torus(machine,t,history,W,H)
                assert candidate.blocks.old_valid(grid,pred)
                lifted=candidate.blocks.lift(grid);word=[None]*N
                for y in range(H):
                    for x in range(W):
                        i=(-h*(x-(W-3))-(h+1)*(y-1))%N
                        assert word[i] is None;word[i]=lifted[y][x]
                assert None not in word and word.count(S)==1 and word[0]==S and word[h*t]==E
                assert all(candidate.blocks.three_valid(word[i],word[(i-h)%N],word[(i-h-1)%N],pred)
                           for i in range(N))
                indices=[h*j%N for j in range(t+1)]
                assert len(set(indices))==t+1 and all(word[i]!=S for i in indices[1:])
                records.append(dict(modulus=modulus,residue=residue,t=t,width=W,height=H,h=h,N=N))
                cases+=1;cells+=N
    after=digest();assert before==after
    return dict(status='PASS_INDEPENDENT_FIXED_UNARY',noncanonical_cyclic_presentations=cases,
                local_triples_checked=cells,records=records,unchanged_sha256=after,
                scope='h=2H or3H and N=(h+1)H; all witnesses have N!=h(h+1), exact unique Start and endpoint ht')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['noncanonical_cyclic_presentations'],'noncanonical cyclic presentations;',
          result['local_triples_checked'],'local triples')
