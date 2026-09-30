"""Reproducible finite checks, not a replacement for the mathematical proofs."""
from __future__ import annotations
from pathlib import Path
import json
import random
from collections import Counter
from padic_machine import *
from quartic_certificate import *


def main():
    rng = random.Random(20260930)
    counts = Counter()
    M = demo_machine()
    for L in range(64):
        for R in range(64):
            assert deinterleave(interleave(L,R)) == (L,R)
            counts['interleave_roundtrips'] += 1
            for q in range(1 << M.r):
                assert M.decode(M.encode(q,L,R)) == (q,L,R)
                counts['configuration_roundtrips'] += 1
    machines = [M]
    for m in (2,3,4,5):
        for _ in range(3):
            rules = {(q,b): Rule(rng.randrange(m),rng.randrange(2),rng.choice('LRS'))
                     for q in range(m-1) for b in (0,1)}
            machines.append(Machine(m,0,m-1,rules))
    for machine in machines:
        streaming = MealyCompiler(machine)
        for n in range(1024):
            k = n.bit_length()+2*machine.K+10
            output = streaming.run((n >> i) & 1 for i in range(k))
            assert sum(bit << i for i,bit in enumerate(output)) == machine.apply(n)
            counts['streaming_full_value_checks'] += 1
        for k in range(13):
            modulus = 1 << (k+1)
            for _ in range(256):
                n = rng.randrange(1 << 16)
                other = n + (rng.randrange(1,17) << k)
                assert (machine.apply(n)-machine.apply(other)) % modulus == 0
                counts['strict_contraction_congruences'] += 1
        for n in range(1,512):
            v = valuation(n)
            f = machine.apply(n)
            assert f == 0 or valuation(f) == v+machine.K
            counts['valuation_drift_checks'] += 1
        for k in range(1,13):
            horizon = (k+machine.K-1)//machine.K
            for _ in range(64):
                x = rng.randrange(1 << k)
                n = x
                for j in range(horizon):
                    x = machine.residue(x,k)
                    n = machine.apply(n)
                    assert x == n % (1 << k)
                    counts['residue_iteration_checks'] += 1
                assert x == 0
                counts['quotient_nilpotence_checks'] += 1
    for T in range(8):
        for S in range(6):
            C = compile_certificate(M,T,S)
            counts['compiled_certificate_shapes'] += 1
            for R in range(1 << S):
                n,w = candidate_witness(C,R)
                q,L,Rnow = M.start,0,R
                for _ in range(T):
                    q,L,Rnow = M.step(q,L,Rnow)
                success = q == M.halt
                assert (C.evaluate(n,w) == 0) == success
                counts['certificate_truth_checks'] += 1
                if success and T in (2,5,7) and S in (0,3,5):
                    for name in C.variables:
                        altered = dict(w); altered[name] += 1
                        assert C.evaluate(n,altered) != 0
                        counts['single_coordinate_tamper_rejections'] += 1
                    assert C.evaluate(n+1,w) != 0
                    counts['public_input_tamper_rejections'] += 1
    for R in range(32):
        n = M.encode(0,0,R)
        clock = lambda t: (t+1)**2+M.K
        q,L,Rnow = M.start,0,R
        v = 0
        for j in range(3):
            n = M.apply(n,clock)
            if q == M.halt:
                assert n == 0
            else:
                q,L,Rnow = M.step(q,L,Rnow)
                v = clock(v)
                assert n == M.encode(q,L,Rnow) << v
            counts['nonlinear_clock_simulations'] += 1
    C = compile_certificate(M,5,3)
    n,w = candidate_witness(C,7)
    expanded = sum((p*p for _,p in C.residuals),Poly())
    assert expanded.degree == 4
    assert expanded.evaluate(dict(w,n=n)) == 0
    counts['expanded_quartic_checks'] += 1
    root = Path(__file__).resolve().parents[1]
    examples = root/'examples'; examples.mkdir(exist_ok=True)
    table = MealyCompiler(M).table()
    assert len(table['states']) <= 2**(2*M.r+8)+6*2**(M.r+5)+2
    (examples/'demo_mealy.json').write_text(json.dumps(table,indent=2)+'\n')
    (examples/'demo_quartic.json').write_text(json.dumps(C.json(),indent=2)+'\n')
    (examples/'demo_witness.json').write_text(json.dumps({'n':n,'witness':w},indent=2)+'\n')
    (examples/'demo_expanded_quartic.json').write_text(json.dumps({
        'degree':expanded.degree,'variables':['n']+C.variables,
        'terms':expanded.json()},indent=2)+'\n')
    orbit=[]
    n=M.encode(0,0,7)
    for j in range(8):
        orbit.append({'time':j,'integer':n,'valuation':None if n == 0 else valuation(n)})
        n=M.apply(n)
    report={'seed':20260930,'all_checks_passed':True,'counts':dict(counts),
            'total_checks':sum(counts.values()),'machine_tables_tested':len(machines),
            'demo_mealy_reachable_states':len(table['states']),
            'demo_witnesses':len(C.variables),'demo_residuals':len(C.residuals),
            'demo_expanded_monomials':len(expanded.terms),'demo_orbit':orbit,
            'scope':'Finite exact checks only. No universal TM table or Lean proof is claimed.'}
    (root/'verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
