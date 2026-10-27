#!/usr/bin/env python3
"""Independent exact checks and wall-clock comparisons for packet extraction."""
from __future__ import annotations
import argparse
from dataclasses import asdict
import itertools
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

from baseline_packet_extraction import (RingSpec, coefficient_finite_difference,
                                       coefficient_reference)
from streamed_coefficients import coefficient_gray, coefficient_antipodal_gray, gray_changes


def validate():
    grids = cases = scalars = odd = even = impossibles = 0
    for dimension in range(1, 5):
        for limits in itertools.product(range(4), repeat=dimension):
            digits = [0] * dimension
            points = [tuple(digits)]
            for j, delta in gray_changes(limits):
                digits[j] += delta
                if not 0 <= digits[j] <= limits[j]:
                    raise AssertionError("Gray point outside box")
                points.append(tuple(digits))
            expected = set(itertools.product(*(range(x+1) for x in limits)))
            if set(points) != expected or len(points) != len(expected):
                raise AssertionError("Gray traversal omitted or repeated a point")
            grids += 1
    rng = random.Random(20261026)
    rings = [RingSpec(), RingSpec((1,1,1),1), RingSpec((0,1),3),
             RingSpec((1,1,1),2), RingSpec((-2,-1,1),2)]
    # Exhaustive binary coefficient choices for small scalar inputs.
    for R, q in [(1,1),(2,1),(2,2),(3,1)]:
        for raw in itertools.product(range(2), repeat=R*(q+1)):
            forms = [tuple((raw[r*(q+1)+j],) for j in range(q+1)) for r in range(R)]
            for beta in itertools.product(range(R+1), repeat=q):
                if sum(beta) > R: continue
                for p in (1,3):
                    expected = coefficient_reference(forms,beta,p)
                    a = coefficient_gray(forms,beta,p)
                    b = coefficient_antipodal_gray(forms,beta,p)
                    if a.coefficient != expected or b.coefficient != expected:
                        raise AssertionError((forms,beta,p,expected,a,b))
                    scalars += 1
    for ring in rings:
        for R in range(0,9):
            for q in range(0,5):
                for trial in range(4):
                    p=rng.randrange(1,20)
                    beta=[0]*q
                    if q:
                        for _ in range(rng.randrange(R+2)):
                            beta[rng.randrange(q)] += 1
                    forms=[tuple(tuple(rng.randrange(-(1<<p),1<<p)
                         for _ in range(ring.dimension)) for _ in range(q+1)) for _ in range(R)]
                    expected=coefficient_reference(forms,beta,p,ring)
                    baseline=coefficient_finite_difference(forms,beta,p,ring)
                    a=coefficient_gray(forms,beta,p,ring)
                    b=coefficient_antipodal_gray(forms,beta,p,ring)
                    if not (baseline.coefficient == a.coefficient == b.coefficient == expected):
                        raise AssertionError((R,q,beta,p,ring,expected,a,b))
                    if sum(beta)>R: impossibles+=1
                    elif any(x%2 for x in a.homogenized_exponents): odd+=1
                    else: even+=1
                    cases+=1
    squarefree_identity=[[(0,),(1,),(0,)],[(0,),(0,),(1,)]]
    precision_case=coefficient_antipodal_gray(squarefree_identity,(1,1),1)
    # Half-grid numerator=2. Reducing at p=1 before division would give 0.
    insufficient_precision_answer=((2 % 2)//2) % 2
    if precision_case.coefficient!=(1,) or insufficient_precision_answer!=0:
        raise AssertionError("precision negative control changed")
    even_identity=[[(0,),(1,)],[(0,),(1,)]]
    even_case=coefficient_antipodal_gray(even_identity,(2,),1)
    if even_case.working_precision!=1 or even_case.coefficient!=(1,):
        raise AssertionError("all-even precision saving failed")
    return {"gray_boxes_exhaustively_checked":grids,"exhaustive_scalar_cases":scalars,
            "random_exact_comparisons":cases,"odd_exponent_cases":odd,
            "all_even_exponent_cases":even,"impossible_degree_cases":impossibles,
            "rings":[asdict(ring) for ring in rings],"random_seed":20261026,
            "precision_negative_control":{"expected":1,"insufficient_precision":0,
              "working_precision":precision_case.working_precision,"input_precision":1},
            "all_even_precision_saving":{"expected":1,"working_precision":1,
               "baseline_working_precision":2,"evaluations":even_case.evaluation_count},
            "methods":["independent direct polynomial DP","shipped finite differences",
                       "Gray finite differences","antipodal Gray polarization"]}


def benchmark(repeats=3):
    rng = random.Random(202610261)
    specs=[]
    for R in (6,8,10,12,14):
        specs.append(("squarefree",R,(1,)*R,32,RingSpec()))
    for R in (6,12,18):
        specs.append(("multiplicity-two",R,(2,)*(R//2),32,RingSpec()))
    for R in (12,24,48):
        specs.append(("three-modes",R,(R//3,)*3,64,RingSpec()))
    specs.extend([
       ("quadratic-extension",10,(1,)*10,48,RingSpec((1,1,1),1)),
       ("nilpotent-extension",8,(1,)*8,48,RingSpec((1,1,1),2)),
       ("mixed-exponents",15,(1,2,3,4,5),48,RingSpec()),
       ("one-odd-exponent",13,(1,2,2,2,2,2,2),32,RingSpec()),
       ("zero-heavy",12,(4,4,4)+(0,)*61,32,RingSpec()),
       ("one-mode",32,(16,),64,RingSpec()),
       ("low-precision",12,(1,)*12,1,RingSpec()),
       ("high-precision",12,(1,)*12,256,RingSpec()),
    ])
    methods=[("baseline",coefficient_finite_difference),("gray",coefficient_gray),
             ("antipodal_gray",coefficient_antipodal_gray)]
    output=[]
    for family,R,beta,p,ring in specs:
        forms=[tuple(tuple(rng.randrange(1<<p) for _ in range(ring.dimension))
                    for _ in range(len(beta)+1)) for _ in range(R)]
        reference=coefficient_reference(forms,beta,p,ring)
        timings={name:[] for name,_ in methods}
        observations={}
        # Rotate execution order to reduce persistent order effects.
        for repetition in range(repeats):
            ordered=methods[repetition%3:]+methods[:repetition%3]
            for name,method in ordered:
                start=time.perf_counter()
                result=method(forms,beta,p,ring)
                elapsed=time.perf_counter()-start
                if result.coefficient != reference:
                    raise AssertionError((family,R,name,"benchmark mismatch"))
                timings[name].append(elapsed)
                observations[name]=asdict(result)
        median={name:statistics.median(values) for name,values in timings.items()}
        row={"family":family,"R":R,"beta":list(beta),"p":p,"ring":asdict(ring),
             "seconds":timings,"median_seconds":median,
             "speedup_gray":median["baseline"]/median["gray"],
             "speedup_antipodal":median["baseline"]/median["antipodal_gray"],
             "observations":observations}
        output.append(row)
        print(json.dumps({k:row[k] for k in ("family","R","median_seconds",
                "speedup_gray","speedup_antipodal")}),flush=True)
    return {"scope":"Packet coefficient kernel; these are not SAT solve times.",
            "python":sys.version,"platform":platform.platform(),"repetitions":repeats,
            "seed":202610261,"rows":output}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/"results/local_checks")
    parser.add_argument("--repeats",type=int,default=3)
    parser.add_argument("--validation-only",action="store_true")
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    checks=validate()
    (args.output/"verification.json").write_text(json.dumps(checks,indent=2)+"\n")
    print(json.dumps({"verification":checks}),flush=True)
    if not args.validation_only:
        data=benchmark(args.repeats)
        (args.output/"benchmarks.json").write_text(json.dumps(data,indent=2)+"\n")


if __name__=="__main__":main()
