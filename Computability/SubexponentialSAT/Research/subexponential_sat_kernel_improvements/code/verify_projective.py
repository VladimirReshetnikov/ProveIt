#!/usr/bin/env python3
"""Exact independent verification of the projective mixed-radix kernel."""
from __future__ import annotations
from dataclasses import asdict
import itertools
import json
from pathlib import Path
import random
import argparse

from baseline_packet_extraction import RingSpec, coefficient_reference, coefficient_finite_difference
from streamed_coefficients import coefficient_antipodal_gray
from projective_coefficients import coefficient_projective_12


def compare(forms,beta,p,ring,root=None):
    expected=coefficient_reference(forms,beta,p,ring)
    old=coefficient_finite_difference(forms,beta,p,ring)
    centered=coefficient_antipodal_gray(forms,beta,p,ring)
    projective=coefficient_projective_12(forms,beta,p,ring,cube_root=root)
    if not expected == old.coefficient == centered.coefficient == projective.coefficient:
        raise AssertionError((forms,beta,p,ring,expected,old,centered,projective))
    return projective


def verify():
    exhaustive=random_cases=0
    ring=RingSpec((1,1,1),1)
    for b in [(1,), (2,), (1,1), (1,2), (2,1), (2,2), (1,1,1), (0,2,2)]:
        R=sum(b)
        for raw in itertools.product(range(2),repeat=R*len(b)):
            forms=[tuple((raw[r*len(b)+j],0) for j in range(len(b))) for r in range(R)]
            for p in (1,3):
                compare(forms,b[1:],p,ring)
                exhaustive+=1
    rng=random.Random(202610262)
    rings=[(RingSpec((1,1,1),1),None),(RingSpec((1,1,1),2),None),
           (RingSpec((1,0,1,0,1),1),(0,0,1,0))]
    for ring,root in rings:
        for q in range(1,6):
            for trial in range(50):
                b=tuple(rng.randrange(3) for _ in range(q))
                R=sum(b)
                p=rng.randrange(1,65)
                forms=[tuple(tuple(rng.randrange(-(1<<p),1<<p)
                                  for _ in range(ring.dimension)) for _ in range(q)) for _ in range(R)]
                compare(forms,b[1:],p,ring,root)
                random_cases+=1
    # All-squarefree cases need no cube root, even in a scalar/nilpotent ring.
    for ring in (RingSpec(),RingSpec((0,1),3),RingSpec((-2,-1,1),2)):
        for R in range(1,8):
            for p in (1,5,23):
                forms=[tuple(tuple(rng.randrange(1<<p) for _ in range(ring.dimension))
                             for _ in range(R)) for _ in range(R)]
                compare(forms,(1,)*(R-1),p,ring)
                random_cases+=1
    special=compare([],(),1,RingSpec())
    impossible=compare([[(1,0),(1,0)]],(2,),2,RingSpec((1,1,1)))
    if special.coefficient!=(1,) or impossible.coefficient!=(0,0):
        raise AssertionError("zero degree or impossible target failed")

    errors=[]
    tests=[
      ("unsupported exponent", lambda: coefficient_projective_12([[(1,)]]*3,(),2,RingSpec())),
      ("missing cube root", lambda: coefficient_projective_12([[(1,),(1,)]]*4,(2,),2,RingSpec())),
      ("incorrect cube root", lambda: coefficient_projective_12([[(1,0),(1,0)]]*4,(2,),2,RingSpec((1,1,1)),cube_root=(1,0))),
      ("root valid only at creation precision", lambda: coefficient_projective_12([[(1,0),(1,0),(1,0)]]*4,(1,2),1,RingSpec((1,1,1)),cube_root=(2,1))),
    ]
    for name,operation in tests:
        try: operation()
        except ValueError: errors.append(name)
        else: raise AssertionError("invalid case was accepted: "+name)
    # A nonminimal pivot would alias x1^3 with the target x0^2*x1.
    wrong_pivot_numerator=sum(x*(x**3) for x in (1,-1))
    if wrong_pivot_numerator//2 != 1:
        raise AssertionError("nonminimal-pivot counterexample changed")
    return {"exhaustive_binary_coefficient_cases":exhaustive,
            "random_exact_four_method_comparisons":random_cases,
            "zero_degree_cases":1,"impossible_degree_cases":1,
            "rejected_invalid_inputs":errors,"random_seed":202610262,
            "rings":[{"ring":asdict(r),"supplied_root":w} for r,w in rings],
            "counterexamples":{"nonminimal_pivot":{"correct":0,"wrong_pivot":1},
                "insufficient_root_precision":{"p":1,"working_precision":2,"root":[2,1],"rejected":True}},
            "methods":["direct truncated polynomial DP","shipped finite differences",
                       "anisotropic antipodal Gray","projective roots of unity"]}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/"results/local_checks/projective_verification.json")
    args=parser.parse_args()
    data=verify()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+"\n")
    print(json.dumps(data))
