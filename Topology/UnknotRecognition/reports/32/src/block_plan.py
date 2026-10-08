"""Syntactically certified four-strand torus blocks and isolated defects.

SPDX-License-Identifier: MIT-0
Pareto dynamic programming over (number of blocks, number of defect letters).
It never treats arbitrary periodic braid words as torus blocks. No group-word
rewriting is used, and a certificate is checked by literal reconstruction.
"""
from __future__ import annotations
from dataclasses import dataclass,asdict
import argparse
import json


@dataclass(frozen=True)
class Piece:
    start: int
    end: int
    kind: str
    pattern: tuple[int,...]
    repetitions: int


def patterns(strands):
    return sorted({tuple(sign*x for x in p)
                   for j in range(1,strands-2)
                   for p in ((j,j+1,j+2),(j+2,j+1,j)) for sign in (1,-1)})


def validate(strands,word):
    if type(strands) is not int or strands<1 or any(type(x) is not int or not 0<abs(x)<strands for x in word):
        raise ValueError('invalid braid')


def verify(strands,word,pieces):
    validate(strands,word)
    allowed=set(patterns(strands)); pos=0; blocks=defects=0
    for p in pieces:
        if not isinstance(p,Piece): raise ValueError('expected a Piece')
        if p.start!=pos or type(p.repetitions) is not int or p.repetitions<1:
            raise ValueError('invalid certificate coverage')
        if p.kind=='block':
            if p.pattern not in allowed: raise ValueError('not a supported torus pattern')
            blocks+=1
        elif p.kind=='defect':
            if len(p.pattern)!=1 or p.repetitions!=1: raise ValueError('invalid defect')
            defects+=1
        else: raise ValueError('unknown piece kind')
        expansion=list(p.pattern)*p.repetitions
        if p.end!=p.start+len(expansion) or word[p.start:p.end]!=expansion:
            raise ValueError('certificate does not reconstruct the source')
        pos=p.end
    if pos!=len(word): raise ValueError('certificate omits a suffix')
    return blocks,defects


def plan(strands,word):
    """Return every nondominated (t,d) with a reconstructible witness.

    Worst-case deliberately simple polynomial DP, O(s n^4) elementary work
    and O(n^2) retained labels plus backpointers; not a wall-time optimizer.
    """
    validate(strands,word); n=len(word); pats=patterns(strands)
    # For a fixed t, keep only the least d at this prefix, plus its backpointer.
    table=[{} for _ in range(n+1)]
    table[0][0]=(0,None,None)
    for i in range(n):
        # Delete labels dominated by fewer blocks and no more defects.
        best=n+1
        for t in sorted(list(table[i])):
            if table[i][t][0]>=best: del table[i][t]
            else: best=table[i][t][0]
        edges=[Piece(i,i+1,'defect',(word[i],),1)]
        for pat in pats:
            end=i
            while end+3<=n and tuple(word[end:end+3])==pat:
                end+=3; edges.append(Piece(i,end,'block',pat,(end-i)//3))
        for t,(d,_,_) in list(table[i].items()):
            for p in edges:
                tt=t+(p.kind=='block'); dd=d+(p.kind=='defect')
                old=table[p.end].get(tt)
                if old is None or dd<old[0]: table[p.end][tt]=(dd,(i,t),p)
    answers=[]; best=n+1
    for t,(d,_,_) in sorted(table[n].items()):
        if d>=best: continue
        best=d; pos=n; tt=t; pieces=[]
        while pos:
            _,prev,p=table[pos][tt]; pieces.append(p); pos,tt=prev
        pieces.reverse(); assert verify(strands,word,pieces)==(t,d)
        answers.append({'blocks':t,'defects':d,'pieces':pieces})
    return answers


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--strands',type=int,required=True); p.add_argument('--word',required=True)
    a=p.parse_args(); result=plan(a.strands,json.loads(a.word))
    print(json.dumps([dict(r,pieces=[asdict(p) for p in r['pieces']]) for r in result],indent=2))


if __name__=='__main__': main()
