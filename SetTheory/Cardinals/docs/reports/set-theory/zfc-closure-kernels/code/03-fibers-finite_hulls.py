#!/usr/bin/env python3
"""Finite structural regression checks, not models/proofs of infinite set theory.

Every binary E and every binary matrix relation R is inspected for sizes 1..3.
Arbitrary R is appropriate here: on a finite equality-bearing domain it can be
specified by a formula with finitely many parameters. All tests use bitsets.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json


def cols(n: int, code: int) -> tuple[int,...]:
    mask=(1<<n)-1
    return tuple((code>>(n*x))&mask for x in range(n))


def bounded(n: int, e: tuple[int,...], r: tuple[int,...], subset: bool) -> bool:
    bounds = tuple(sum(1<<y for y in range(n) if not (e[y]&~e[b]))
                   for b in range(n)) if subset else e
    return all(any(not (fiber&~b) for b in bounds) for fiber in r)


def efh(n: int, e: tuple[int,...], r: tuple[int,...], exact: bool=True) -> bool:
    good=[]
    for v in range(n):
        inside=[x for x in range(n) if e[v]>>x&1]
        good.append(all(not(e[x]&~e[v]) and
            any((e[b]==r[x] if exact else not(r[x]&~e[b])) for b in inside)
            for x in inside))
    return all(any((e[v]>>a&1) and good[v] for v in range(n)) for a in range(n))


def closure(n: int,e: tuple[int,...],r: tuple[int,...],rooted: bool) -> bool:
    good=[all(not(r[x]&~e[v]) for x in range(n) if e[v]>>x&1)
          for v in range(n)]
    return all(any(good[v] and ((e[v]>>a&1) if rooted else not(e[a]&~e[v]))
                   for v in range(n)) for a in range(n))


def separation(n: int,e: tuple[int,...]) -> bool:
    return all(any(c==(e[a]&s) for c in e) for a in range(n) for s in range(1<<n))


def run() -> dict:
    rows=[]; comparisons=0
    for n in range(1,4):
        full=1<<(n*n)
        counts=dict(extensional=0, Ext_all_EFH=0,
                    Ext_all_weakened_EFH=0, Ext_Sep_all_element_TC=0,
                    Ext_Sep_all_rooted_TC=0)
        for ec in range(full):
            e=cols(n,ec); ext=len(set(e))==n
            if ext: counts['extensional']+=1
            all_efh=all_weak=all_element=all_root=True
            for rc in range(full):
                r=cols(n,rc); comparisons+=1
                bs=bounded(n,e,r,True); bm=bounded(n,e,r,False)
                if bs:
                    all_efh &= efh(n,e,r)
                    all_weak &= efh(n,e,r,False)
                if bm:
                    all_element &= closure(n,e,r,False)
                    all_root &= closure(n,e,r,True)
                # Rooted closure implies element-seeded closure if e is transitive
                # is NOT a general implication. No such assertion is tested here.
            if ext:
                counts['Ext_all_EFH']+=all_efh
                counts['Ext_all_weakened_EFH']+=all_weak
                if separation(n,e):
                    counts['Ext_Sep_all_element_TC']+=all_element
                    counts['Ext_Sep_all_rooted_TC']+=all_root
        rows.append(dict(n=n,membership_relations=full,matrix_relations_each=full,**counts))
    # Two explicit all-instance countermodels.
    e=(0,)
    for r in ((0,),(1,)):
        assert not bounded(1,e,r,False) or closure(1,e,r,False)
        assert not bounded(1,e,r,True) or closure(1,e,r,False)
        assert not closure(1,e,r,True)
    e=(1,)
    for r in ((0,),(1,)):
        assert efh(1,e,r,False)
    assert not efh(1,(1,),(0,),True)
    result={'E_R_pairs_tested':comparisons,'rows':rows,
        'empty_one_object_model':'Ext + full Separation + element-seeded member/subset closure; rooted closure fails.',
        'universal_one_object_model':'Ext + all weakened-EFH instances; exact-EFH false-matrix instance fails.',
        'scope':'Exhaustive sizes 1..3 only. Not a PA proof or a proof of consistency of EFH.'}
    root=Path(__file__).resolve().parents[1]
    (root/'results').mkdir(exist_ok=True)
    (root/'results/finite_hulls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    return result

if __name__=='__main__':run()
