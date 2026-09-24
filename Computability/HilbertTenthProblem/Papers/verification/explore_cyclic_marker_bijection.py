#!/usr/bin/env python3
"""Canonical Start/End bijection in the genuine fixed helical relation."""
from collections import Counter
from itertools import product
from pathlib import Path
from math import gcd
import hashlib,json,sys
import explore_fixed_raw_universal_81 as old

OUT=Path(__file__).with_suffix('.json')
ROOT=Path(__file__).resolve().parents[2]


def verify_phase_cycles():
    edges={'V':('L',),'L':('L','I'),'I':('I','Q'),'Q':('R',),'R':('R','V')}
    counts=Counter()
    for N in range(1,19):
        for initial in edges:
            def visit(word):
                if len(word)<N:
                    for nxt in edges[word[-1]]:visit(word+[nxt])
                    return
                if initial not in edges[word[-1]]:return
                starts={i for i in range(N) if tuple(word[(i+j)%N] for j in (-1,0,1))==('I','I','Q')}
                ends={i for i in range(N) if tuple(word[(i+j)%N] for j in (-1,0,1))==('L','I','I')}
                mapping={}
                for s in starts:
                    e=s;steps=0
                    while word[(e-1)%N]=='I':
                        e=(e-1)%N;steps+=1
                        assert steps<N
                    assert e in ends and steps>=1
                    back=e;backsteps=0
                    while word[(back+1)%N]=='I':
                        back=(back+1)%N;backsteps+=1
                        assert backsteps<N
                    assert back==s and backsteps==steps
                    mapping[s]=e
                    counts['paired_markers']+=1
                    counts['runs_crossing_numeric_origin']+=int(e>s)
                assert set(mapping.values())==ends and len(mapping)==len(set(mapping.values()))
                if len(ends)==1:assert len(starts)==1
                counts['unique_end_words']+=int(len(ends)==1)
                counts['multiple_marker_words']+=int(len(ends)>1)
                counts['short_unmarked_I_runs']+=sum(tuple(word[(i+j)%N] for j in (-1,0,1))==('L','I','Q') for i in range(N))
                counts['closed_phase_words']+=1
            visit([initial])
    assert counts['closed_phase_words']==34923 and counts['paired_markers']==36976
    return dict(counts,maximum_length=18,
                scope='Initialization phase graph; not an enumeration of all tableau tiles')


def verify_word(word,h,machine):
    blocks=old.helical.lift_word(word,h);N=len(word)
    pred=old.helical.predicate(machine);S,E=old.fixed_markers(machine)
    assert all(pred(block) for block in blocks)
    assert all(old.unary.blocks.three_valid(blocks[i],blocks[(i-1)%N],blocks[(i-h)%N],pred) for i in range(N))
    starts={i for i,b in enumerate(blocks) if b==S}
    ends={i for i,b in enumerate(blocks) if b==E}
    mapping={};wrapped=0
    for s in starts:
        e=s;steps=0
        while word[(e+1)%N][3]=='I':
            e=(e+1)%N;steps+=1
            assert steps<N
        assert e in ends and steps>=1 and steps==(e-s)%N
        back=e;backsteps=0
        while word[(back-1)%N][3]=='I':
            back=(back-1)%N;backsteps+=1
            assert backsteps<N
        assert back==s and backsteps==steps
        mapping[s]=e;wrapped+=int(e<s)
    assert set(mapping.values())==ends and len(mapping)==len(set(mapping.values()))
    if len(ends)==1:assert len(starts)==1
    return dict(triples=N,paired_markers=len(mapping),origin_crossings=wrapped,
                unique_end=int(len(ends)==1),unmarked=int(not ends),multiple_pairs=int(len(ends)>1),
                noncanonical_stride=int(N%h!=0))


def verify_helical_words():
    counts=Counter()
    for modulus,residue in ((1,0),(2,0)):
        machine=old.residue_machine(modulus,residue)
        for run in range(1,7):
            history=old.unary.history_for(machine,run,limit=24)
            if history[-1][2]!=machine.halt:continue
            wmin,hmin=old.unary.thresholds(history,run)
            for dw,dh,factor in product(range(2),range(2),(1,2,3)):
                width,height=wmin+dw,hmin+dh
                if gcd(factor,height)!=1:continue
                h=factor*width
                grid=old.helical.strip_array(machine,run,history,width,height)
                word=old.cyclic_word(grid,h)
                for repeat in (1,2):
                    repeated=word*repeat
                    for rotation in (0,1,len(repeated)-1):
                        shifted=repeated[rotation:]+repeated[:rotation]
                        record=verify_word(shifted,h,machine)
                        assert record['paired_markers']==(0 if run==1 else repeat)
                        counts.update(record);counts['presentations']+=1
    assert counts['noncanonical_stride'] and counts['origin_crossings'] and counts['unmarked']
    return dict(counts,scope='Genuine valid windows, both overlaps, rotations and repetitions; includes h not dividing N')


def verify():
    paths=['Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md',
           'Papers/verification/explore_fixed_raw_universal_81.py',
           'Papers/verification/explore_helical_unary_tableau.py']
    return dict(status='PASS_CYCLIC_MARKER_BIJECTION',phase_cycles=verify_phase_cycles(),
                helical_words=verify_helical_words(),
                dependencies_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                proof='../1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md',
                conclusion='Unique End implies unique Start on cyclic residues; known Start0 supplies the old semantic interface',
                arithmetic_operation_bound_claimed=False)


if __name__=='__main__':
    result=verify();normalized=json.loads(json.dumps(result))
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert normalized==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['phase_cycles']['closed_phase_words'],result['helical_words']['presentations'])
