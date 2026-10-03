"""Deterministic regression / exhaustive checks and reproducible artifact export."""
from __future__ import annotations
import copy
import itertools
import json
import random
from pathlib import Path
from spectral_guards import (Mode, Sequence, Block, build_certificate,
    verify_certificate, brute_chart, tail_threshold, first_negative)
from quartic_compiler import compile_certificate, verify_export

ROOT=Path(__file__).resolve().parents[1]

def run() -> dict:
    counts={"exhaustive_chart_instances":0,"random_chart_instances":0,
            "ladder_identity_checks":0,"forged_chart_rejections":0,
            "tail_sign_checks":0,"polynomial_assignments":0,
            "single_coordinate_mutation_rejections":0,
            "serialization_checks":0,"shape_uniformity_checks":0}
    rng=random.Random(20261002)
    for coefficients in itertools.product(range(-3,4),repeat=3):
        seq=Sequence(tuple(Mode(b,(c,)) for b,c in zip((1,2,3),coefficients)))
        for T in range(9):
            cert=build_certificate(seq,T)
            assert verify_certificate(cert)
            for r,row in enumerate(seq.ladder()):
                expected=[[b.lo,b.hi,b.sign] for b in brute_chart(row,T)]
                assert cert["charts"][r]==expected
            counts["exhaustive_chart_instances"]+=1
    for _ in range(700):
        s=rng.randint(1,3)
        bases=sorted(rng.sample(range(1,8),s))
        lengths=[rng.randint(1,3) for _ in bases]
        seq=Sequence(tuple(Mode(b,tuple(rng.randint(-8,8) for _ in range(n)))
                           for b,n in zip(bases,lengths)))
        T=rng.randint(0,35)
        cert=build_certificate(seq,T)
        assert verify_certificate(cert)
        for r,row in enumerate(seq.ladder()):
            assert cert["charts"][r]==[[b.lo,b.hi,b.sign] for b in brute_chart(row,T)]
            if row.dimension:
                for t in (0,1,T):
                    assert row.step().value(t)==row.value(t+1)-row.modes[0].base*row.value(t)
                    counts["ladder_identity_checks"]+=1
        counts["random_chart_instances"]+=1
        bad=copy.deepcopy(cert)
        bad["charts"][0][0][2]={-1:0,0:1,1:-1}[bad["charts"][0][0][2]]
        assert not verify_certificate(bad)
        counts["forged_chart_rejections"]+=1
    for _ in range(120):
        seq=Sequence(tuple(Mode(b,tuple(rng.randint(-2,2) for _ in range(rng.randint(1,3))))
                           for b in (1,2,3)))
        T,s=tail_threshold(seq)
        for n in (T,T+1,T+2,2*T+1):
            v=seq.value(n)
            assert (v>0)-(v<0)==s
            counts["tail_sign_checks"]+=1

    examples={
      "hidden_negative":(Sequence((Mode(1,(16,)),Mode(2,(-10,)),Mode(4,(1,)))),4),
      "discrete_not_continuous":(Sequence((Mode(1,(8,)),Mode(2,(-6,)),Mode(4,(1,)))),6),
      "jordan_block":(Sequence((Mode(2,(10,-7,1)),)),8),
      "identically_zero":(Sequence((Mode(2,(0,0)),)),4),
    }
    demo_stats={}
    for name,(seq,T) in examples.items():
        cert=build_certificate(seq,T)
        (ROOT/"examples"/(name+".json")).write_text(json.dumps(cert,indent=2)+"\n")
        for bits in (None,max(1,T.bit_length())):
            e=compile_certificate(cert,bits)
            assert not e.failed_residuals()
            counts["polynomial_assignments"]+=1
            suffix="quasi" if bits is None else "quartic"
            demo_stats[name+"_"+suffix]=e.summary()
            # Full symbolic exports for the principal example only.
            if name=="hidden_negative":
                path=ROOT/"examples"/(name+"_"+suffix+".json")
                e.export(path)
                assert verify_export(path)
                counts["serialization_checks"]+=1
            if bits is not None:
                positive=compile_certificate(cert,bits,require_nonnegative=True)
                assert (not positive.failed_residuals()) == (first_negative(cert) is None)
                counts["polynomial_assignments"]+=1
        # Same partition, false sign claim: emitter must reject without relying on generator.
        bad=copy.deepcopy(cert)
        bad["charts"][0][0][2]={-1:0,0:1,1:-1}[bad["charts"][0][0][2]]
        wrong=compile_certificate(bad,max(1,T.bit_length()))
        assert wrong.failed_residuals()
        counts["forged_chart_rejections"]+=1

    # Strong mutation check: every noninput coordinate, both natural +/-1 where possible.
    seq,T=examples["hidden_negative"]
    e=compile_certificate(build_certificate(seq,T),3)
    incidence=[set() for _ in e.values]
    for j,p in enumerate(e.residuals):
        for monomial in p.terms:
            for i in monomial:
                incidence[i].add(j)
    input_ids=set(e.inputs)
    for i,old in enumerate(e.values):
        if i in input_ids:
            continue
        for new in (old+1,old-1):
            if new<0:
                continue
            e.values[i]=new
            assert any(e.residuals[j].evaluate(e.values) for j in incidence[i]), i
            counts["single_coordinate_mutation_rejections"]+=1
        e.values[i]=old
    assert not e.failed_residuals()
    # Same shape and bit bound: coefficients, bases, horizons, chart contents vary.
    baseline=[p.terms for p in e.residuals]
    for _ in range(12):
        bs=sorted(rng.sample(range(1,10),3))
        seq=Sequence(tuple(Mode(b,(rng.randint(-12,12),)) for b in bs))
        cert=build_certificate(seq,rng.randint(0,7))
        other=compile_certificate(cert,3)
        assert baseline==[p.terms for p in other.residuals]
        assert not other.failed_residuals()
        counts["shape_uniformity_checks"]+=1
    # Horizon one million: 1,000,001 time instants and two exact zeros.
    T=1_000_000
    a,b=400,600
    large=Sequence((Mode(1,(2**(a+b),)),Mode(2,(-(2**a+2**b),)),Mode(4,(1,))))
    cert=build_certificate(large,T)
    assert verify_certificate(cert)
    assert cert["charts"][0]==[[0,a-1,1],[a,a,0],[a+1,b-1,-1],[b,b,0],[b+1,T,1]]
    (ROOT/"examples"/"million_step_chart.json").write_text(json.dumps(cert,indent=2)+"\n")
    large_stats={"horizon":T,"top_chart":cert["charts"][0],
                 "occupied_chart_blocks":sum(map(len,cert["charts"])),
                 "slot_bound":large.dimension**2+1,
                 **cert["construction_statistics"]}
    report={"seed":20261002,"counts":counts,"demo_statistics":demo_stats,
            "large_horizon":large_stats,
            "status":"All listed checks passed. Tests are not a formal proof.",
            "implementation_scope":"Scalar polynomial-exponential chart construction, endpoint verification, quasi-system and bounded-bit quartic export; no automatic matrix/Jordan frontend or Lean proof."}
    (ROOT/"validation"/"results.json").write_text(json.dumps(report,indent=2)+"\n")
    return report

if __name__=="__main__":
    print(json.dumps(run(),indent=2))
