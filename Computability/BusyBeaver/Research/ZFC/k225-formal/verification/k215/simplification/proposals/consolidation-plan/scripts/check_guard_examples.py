#!/usr/bin/env python3
"""Finite sanity checks for the supported-collection-to-image lemma.

These checks are not formal proofs or models of ZFC. They illustrate precisely
why the domain guard, image support and output uniqueness must be retained.
"""
import argparse
import itertools
import json
from pathlib import Path

def supported(R,A,B,guard=True):
    S={(x,y) for x,y in R if not guard or x in A}
    return (all(any((x,y) in S for x in range(3)) for y in B)
            and all(not any((x,y) in S for y in range(3)) or
                    any((x,y) in S for y in B) for x in A))

def functional(R,A):
    return all(len({y for u,y in R if u==x})<=1 for x in A)

def exact(R,A,B):
    return B=={y for x,y in R if x in A}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',required=True,type=Path); a=ap.parse_args()
    domain=range(3); subsets=[{i for i in domain if bits>>i&1} for bits in range(8)]
    pairs=list(itertools.product(domain,repeat=2)); checked=valid=0
    for bits in range(1<<9):
        R={p for i,p in enumerate(pairs) if bits>>i&1}
        for A in subsets:
            for B in subsets:
                checked+=1
                if functional(R,A) and supported(R,A,B):
                    valid+=1
                    assert exact(R,A,B)
    examples=[]
    R={(0,0),(1,1)}; A={0}; B={0,1}
    assert functional(R,A) and supported(R,A,B,False) and not exact(R,A,B)
    examples.append({'omitted':'domain guard','relation':sorted(R),'domain':sorted(A),'chosen':sorted(B),'actual_image':[0]})
    R={(0,0),(0,1)}; A={0}; B={0}
    assert supported(R,A,B) and not functional(R,A) and not exact(R,A,B)
    examples.append({'omitted':'functionality','relation':sorted(R),'domain':sorted(A),'chosen':sorted(B),'actual_image':[0,1]})
    R={(0,0)}; A={0}; B={0,1}
    assert functional(R,A) and not supported(R,A,B) and not exact(R,A,B)
    assert all(any((x,y) in R for y in B) for x in A)
    examples.append({'omitted':'image support','relation':sorted(R),'domain':sorted(A),'chosen':sorted(B),'actual_image':[0]})
    result={'scope':'exhaustive finite sanity check on a three-element carrier; not proof-assistant evidence',
            'cases':checked,'cases_satisfying_all_premises':valid,'failures':0,'counterexamples':examples}
    a.out.parent.mkdir(parents=True,exist_ok=True); a.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
