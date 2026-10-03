#!/usr/bin/env python3
"""Finite exact checks; these support, but do not replace, the article's proofs."""
from __future__ import annotations
import itertools as it
import json
import random
import sys
from math import prod
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'code'))
from queue_certificates import (CyclicTag, bits, code, compile_stream, compile_quartic,
                                evaluate, stream_values, resource_guard, tag_values, tag_run,
                                compile_tag, scaled_table_coefficients)
from verify_certificate import verify


def words(B, maximum):
    return [w for n in range(maximum+1) for w in it.product(range(B), repeat=n)]


def main():
    stats = {}
    apps = words(2, 2)
    inputs = words(2, 3)
    cases = raw_spurious = exact_runs = exported_checks = 0
    for ap in it.product(apps, repeat=2):
        p = CyclicTag(ap)
        for w in inputs:
            for T in range(1, 7):
                states, actual = p.run(w, T)
                expected = tuple(actual) if len(actual)==T and not states[-1] else None
                found = []
                for candidate in it.product((0,1), repeat=T):
                    v = stream_values(p, w, candidate)
                    raw = v['length_residual']==0 and v['content_residual']==0
                    legal = raw and v['guard']>=1
                    if raw and not legal:
                        raw_spurious += 1
                    assert legal == (candidate == expected), (ap,w,T,candidate,v,expected)
                    if legal:
                        found.append(candidate)
                    cases += 1
                assert len(found) == (expected is not None)
                if expected is not None:
                    exact_runs += 1
                    for compiler in (compile_stream, compile_quartic):
                        cert = compiler(p,w,T)
                        assert 'witness' in cert
                        ww = list(map(int,cert['witness']))
                        assert evaluate(cert,ww)[0]==0
                        assert verify(cert)['accepted']
                        if compiler is compile_stream:
                            assert len(ww)==T+1
                            assert cert['degree_upper_bound']<=max(4,2*T)
                        else:
                            assert len(ww)==3*T-2
                            assert len(cert['residual_roots'])==3*T
                            assert cert['degree_upper_bound']<=4
                        # Single-coordinate perturbations must be rejected by uniqueness.
                        for j in range(len(ww)):
                            bad = ww.copy();bad[j]+=1
                            assert evaluate(cert,bad)[0]>0
                        exported_checks += 1
    stats['cyclic_tag_candidate_bitstrings']=cases
    stats['uncausal_solutions_rejected']=raw_spurious
    stats['exact_halting_instances']=exact_runs
    stats['valid_compiler_certificates_checked']=exported_checks

    # Exhaust the guard independently, including trajectories negative after failure.
    guard_cases=0
    events=list(it.product(range(3), repeat=2))
    for n in range(4):
        for trace in it.product(events, repeat=3):
            G, legal, _ = resource_guard((n,), [(a,) for a,b in trace], [(b,) for a,b in trace])
            assert G >= 0 and (G>0)==legal and (legal or G==0)
            guard_cases+=1
    rng=random.Random(20260930)
    for _ in range(3000):
        initial=[rng.randrange(5) for _ in range(3)]
        con=[[rng.randrange(4) for _ in range(3)] for _ in range(5)]
        pro=[[rng.randrange(4) for _ in range(3)] for _ in range(5)]
        G, legal, _=resource_guard(initial,con,pro)
        assert G>=0 and (G>0)==legal and (legal or G==0)
        guard_cases+=1
    stats['first_failure_guard_checks']=guard_cases

    # General 2-tag semantics, including nonempty halting tails.
    tag_cases=0
    for ap in it.product(apps,repeat=2):
        for w in inputs:
            for T in range(1,4):
                states, actual=tag_run(ap,2,w,T)
                for terminal in words(2,1):
                    expected=actual if len(actual)==2*T and states[-1]==terminal else None
                    for read in it.product((0,1),repeat=2*T):
                        v=tag_values(ap,2,w,read,terminal)
                        legal=(v['length_residual']==0 and v['content_residual']==0 and v['guard']>0)
                        assert legal==(read==expected), (ap,w,T,terminal,read,v,expected)
                        tag_cases+=1
    for _ in range(30):
        ap=tuple(tuple(rng.randrange(3) for _ in range(rng.randrange(4))) for _ in range(3))
        w=tuple(rng.randrange(3) for _ in range(rng.randrange(5)))
        T=2
        states,actual=tag_run(ap,2,w,T)
        for terminal in words(3,1):
            expected=actual if len(actual)==2*T and states[-1]==terminal else None
            for read in it.product(range(3),repeat=2*T):
                v=tag_values(ap,2,w,read,terminal)
                assert (v['length_residual']==0 and v['content_residual']==0 and v['guard']>0)==(read==expected)
                tag_cases+=1
    stats['general_tag_candidate_words']=tag_cases

    # Zero-slack construction: all bit choices, no hidden existential auxiliaries.
    zero_cases=0
    for ap in [((1,0),()), ((),(1,)), ((0,), (1,1)), ((),())]:
        p=CyclicTag(ap)
        for w in words(2,2):
            for T in range(1,5):
                cert=compile_stream(p,w,T,zero_slack=True)
                states,read=p.run(w,T)
                expected=tuple(read) if len(read)==T and not states[-1] else None
                for b in it.product((0,1),repeat=T):
                    assert (evaluate(cert,b)[0]==0)==(b==expected)
                    zero_cases+=1
    stats['zero_slack_candidate_bitstrings']=zero_cases

    # Exhaust actual natural witness boxes for the quartic, not just generated runs.
    natural_assignments=0
    for ap,w,T,bound in [(((),()),(1,0),2,5), (((1,0),()),(1,),2,5),
                          (((),()),(0,),2,4), (((1,0),()),(1,),3,5)]:
        cert=compile_quartic(CyclicTag(ap),w,T)
        expected=tuple(map(int,cert['witness'])) if 'witness' in cert else None
        zeros=[]
        for ww in it.product(range(bound),repeat=len(cert['variables'])):
            if evaluate(cert,ww)[0]==0:
                zeros.append(ww)
            natural_assignments+=1
        assert zeros==([expected] if expected is not None else []), (ap,w,T,zeros,expected)
    stats['quartic_natural_assignments_exhausted']=natural_assignments

    # All words through length five verify concatenation and both end insertions.
    word_cases=0
    for u in words(2,5):
        U,S=code(u),2**len(u)
        for v in words(2,5):
            V,R=code(v),2**len(v)
            assert (U+S*V,S*R)==(code(u+v),2**len(u+v))
            for a,b in it.product((0,1),repeat=2):
                assert (2*(U+b*S)+a,2*(2*S)) == (2*U+a+b*(2*S),2*(2*S))
            word_cases+=1
    stats['word_monoid_pairs_checked']=word_cases

    # Test exact integer table clearing and the full symbolic deletion-tag compiler.
    from math import factorial
    interpolation_checks = 0
    for B in range(2,5):
        K = factorial(B-1)
        for table in it.product(range(3),repeat=B):
            coefficients = scaled_table_coefficients(table)
            for digit in range(B):
                assert sum(a*digit**j for j,a in enumerate(coefficients)) == K*table[digit]
                interpolation_checks += 1
    stats['integer_interpolation_checks'] = interpolation_checks
    compiled_tag_cases = compiled_tag_certificates = 0
    for B in range(2,5):
        for d in (1,2):
            for _ in range(10):
                ap = tuple(tuple(rng.randrange(B) for _ in range(rng.randrange(4))) for _ in range(B))
                w = tuple(rng.randrange(B) for _ in range(rng.randrange(6)))
                for T in (1,2):
                    states,actual = tag_run(ap,d,w,T)
                    terminal = states[-1]
                    expected = actual if len(actual)==d*T else None
                    cert = compile_tag(ap,d,w,T,terminal)
                    assert len(cert['variables']) == d*T+1
                    assert len(cert['residual_roots']) == d*T+3
                    assert cert['degree_upper_bound'] <= 2*max(B,T*(B-1),d*(T-1)*(B-1),1)
                    if expected is not None:
                        assert verify(cert)['accepted']
                    else:
                        assert 'witness' not in cert
                    for read in it.product(range(B),repeat=d*T):
                        values = tag_values(ap,d,w,read,terminal)
                        u = max(0,values['guard']-1)
                        assert (evaluate(cert,list(read)+[u])[0]==0)==(read==expected)
                        compiled_tag_cases += 1
                    symbolic = compile_tag(ap,d,w,T,terminal,attach_witness=False)
                    assert 'witness' not in symbolic
                    assert symbolic['nodes']==cert['nodes']
                    assert symbolic['residual_roots']==cert['residual_roots']
                    compiled_tag_certificates += 1
    stats['integer_tag_compiler_certificates'] = compiled_tag_certificates
    stats['integer_tag_compiler_candidate_words'] = compiled_tag_cases

    # Explicit documented positive and negative examples.
    p=CyclicTag.parse(['10',''])
    examples=[]
    for name,cert in [('stream_example',compile_stream(p,bits('1'),3)),
                      ('quartic_example',compile_quartic(p,bits('1'),3)),
                      ('zero_slack_example',compile_stream(p,bits('1'),3,zero_slack=True))]:
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(cert,indent=2)+'\n')
        examples.append(verify(cert))
    bad=CyclicTag.parse(['','1'])
    spurious=stream_values(bad,bits('0'),(0,1))
    assert spurious['content_residual']==spurious['length_residual']==0 and spurious['guard']==0
    (ROOT/'examples'/'uncausal_counterexample.json').write_text(json.dumps({
        'appendants':['','1'],'initial':'0','horizon':2,'candidate_read_bits':[0,1],
        'formulas':spurious,'actual_states':['0',''],
        'explanation':'The global word equation holds, but the machine halted after one step.'},indent=2)+'\n')
    ternary = compile_tag(((),(2,0),(0,)),2,(1,0),2,(0,))
    (ROOT/'examples'/'ternary_tag_example.json').write_text(json.dumps(ternary,indent=2)+'\n')
    examples.append(verify(ternary))
    stats['example_verification']=examples
    stats['status']='all exact checks passed'
    (ROOT/'tests'/'results.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))

if __name__=='__main__':
    main()
