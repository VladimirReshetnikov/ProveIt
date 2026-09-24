"""Exact periodic preimages of c XOR (north AND east).

All p-by-q targets with 1<=p,q<=3 are checked. The companion proof
establishes the theorem for all periods and the finite-alphabet extension.
"""

from collections import Counter
import json
from math import lcm
from pathlib import Path


def construct(p, q, target):
    K = lcm(p,q)

    def target_at(i,j):
        return (target >> ((j % q)*p+(i % p))) & 1

    target_rows = [sum(target_at(s,t-s) << s for s in range(K))
                   for t in range(q)]

    def phi(t,state):
        next_bit = (state >> 1) | ((state & 1) << (K-1))
        return target_rows[t % q] ^ (state & next_bit)

    def phase_composition(state):
        for t in range(q-1,-1,-1):
            state = phi(t,state)
        return state

    visited = {}
    state = 0
    while state not in visited:
        visited[state] = len(visited)
        assert len(visited) <= 1 << K
        state = phase_composition(state)
    cycle_start = state
    ell = len(visited)-visited[state]
    assert 1 <= ell <= 1 << K
    T = q*ell
    rows = [0]*(T+1)
    rows[T] = cycle_start
    for t in range(T-1,-1,-1):
        rows[t] = phi(t,rows[t+1])
    assert rows[0] == rows[T]
    rows.pop()

    def preimage_at(i,j):
        return (rows[(i+j) % T] >> (i % K)) & 1

    # Direct diagonal seam checks, including width/height one.
    for t in range(T):
        assert rows[t] == phi(t,rows[(t+1) % T])
    H = lcm(K,T)
    assert T <= q*(1 << K) and H <= K*q*(1 << K)
    assert H % p == 0 and T % q == 0
    sites = 0
    for j in range(T):
        for i in range(H):
            center = preimage_at(i,j)
            north = preimage_at(i,j+1)
            east = preimage_at(i+1,j)
            assert center ^ (north & east) == target_at(i,j)
            assert preimage_at(i+H,j) == center
            assert preimage_at(i,j+T) == center
            assert preimage_at(i+K,j-K) == center
            sites += 1
    return dict(target_width=p,target_height=q,target_code=target,
                diagonal_width=K,composition_cycle_length=ell,
                visited_states=len(visited),horizontal_period=H,
                vertical_period=T,diagonal_rows=rows,verified_sites=sites)


def verify():
    cases = [construct(p,q,target)
             for p in range(1,4) for q in range(1,4)
             for target in range(1 << (p*q))]
    assert len(cases) == 682
    by_period = Counter((c['target_width'],c['target_height']) for c in cases)
    assert by_period[(3,3)] == 512
    ones = next(c for c in cases if (c['target_width'],c['target_height'],c['target_code']) == (1,1,1))
    assert ones['composition_cycle_length'] == 2
    assert ones['horizontal_period'] == ones['vertical_period'] == 2
    assert sorted(ones['diagonal_rows']) == [0,1]
    assert all((c ^ (c & c)) == 0 for c in (0,1))
    return dict(
        status='PASS_EVERY_PERIODIC_TARGET_HAS_A_PERIODIC_PREIMAGE',
        rule='image(i,j)=x(i,j) XOR (x(i,j+1) AND x(i+1,j))',
        scope='Exact finite verification for all specified target periods at most3; the companion finite-state proof establishes arbitrary periods. No hardness or universality claim.',
        total_period_presentations=len(cases),
        target_counts_by_period={str(k):v for k,v in sorted(by_period.items())},
        max_cycle_length=max(c['composition_cycle_length'] for c in cases),
        max_horizontal_period=max(c['horizontal_period'] for c in cases),
        max_vertical_period=max(c['vertical_period'] for c in cases),
        total_verified_sites=sum(c['verified_sites'] for c in cases),
        constant_one_target_requires_period_growth=True,
        cases=cases,
        proof='../1980/EXPLORATION_TOFFOLI_PERIODIC_PREIMAGES.md')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(receipt['status'])
    print(receipt['total_period_presentations'], 'target presentations;',
          receipt['total_verified_sites'], 'direct torus-site checks; max cycle',
          receipt['max_cycle_length'])
