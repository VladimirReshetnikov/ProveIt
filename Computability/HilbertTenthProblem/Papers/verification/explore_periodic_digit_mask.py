#!/usr/bin/env python3
"""Exact periodic-mask popcount identities and outer-operation counts."""
import json
from pathlib import Path


def verify():
    cases,overflows = 0,0
    for N in range(1,9):
        L = 4**N
        M = 2*(L-1)//3
        assert M.bit_count() == N
        for P in range(L):
            r = (L-P)*(L-1)+M
            carries = P.bit_count()+M.bit_count()-(P+M).bit_count()
            correction = 0
            if P+M >= L:
                correction = (P & -P).bit_length()-1
                overflows += 1
            assert r.bit_count() == 3*N-carries-correction
            assert (r.bit_count() >= 3*N) == (P&M == 0)
            assert (r&1) == (P&1)
            cases += 1
    bounds = []
    for q in (2,4,5,7,8,10,16):
        Q = q*q
        L = Q**8
        assert (L-1)%3 == 0
        lam = (L-1)//3
        N0,D = Q**6,Q**12
        assert D == L*Q**4 == N0*N0
        for P in (0,1,Q**5-1,Q**6-1):
            r = (L-P)*(L-1)+2*lam
            assert 0 <= P < Q**6 < L
            assert N0*N0 < r < Q**16 < N0**3
            assert 4*r < D*D//2
        bounds.append({'q':q,'Q':Q,'pre_power_size_bounds':True})
    # Exact fourth-radix examples for the low-edge-plane mechanism.
    edges = 0
    for N in range(2,7):
        Q = 4**N
        for stride in range(1,N+1):
            if N%stride: continue
            W=4**stride
            h=(Q-1)//(W-1)
            h_digits=[(h//4**j)%4 for j in range(N)]
            assert set(h_digits) <= {0,1}
            for word in range(min(Q//4,512)):
                digits=[(word//4**j)%4 for j in range(N)]
                if any(d>1 for d in digits): continue
                total=word+h
                total_boolean=all((total//4**j)%4 <= 1 for j in range(N))
                assert total < Q
                assert total_boolean == (word&h == 0)
                if total_boolean: assert word%2 == 0
                edges += 1
    return dict(status='PASS',periodic_predicate_cases=cases,
                overflowing_addition_cases=overflows,pre_power_bound_cases=bounds,
                edge_plane_cases=edges,
                outer_operation_counts={
                    'generic_mask_with_shared_scale':14,
                    'special_mask_with_explicit_N0':12,
                    'special_mask_if_only_scale_D_is_used':11,
                    'optional_sixth_plane_increment':3},
                scope='Exact finite corroboration of the general popcount lemma and local outer arithmetic/edge-plane arguments, not a complete universal-machine certificate.',
                proof='../1980/EXPLORATION_PERIODIC_DIGIT_MASK.md')


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['periodic_predicate_cases'],'periodic predicates;',
          result['edge_plane_cases'],'edge-plane cases',flush=True)
