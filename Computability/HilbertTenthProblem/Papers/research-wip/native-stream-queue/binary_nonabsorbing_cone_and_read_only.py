#!/usr/bin/env python3
"""Exact finite-graph comparisons for proved nonabsorbing-controller bounds."""
import argparse
from collections import deque
import json
from pathlib import Path
import random

ROWS = ((0, 0), (0, 1), (1, 0))


def queue_graph(a, b, g, I, m):
    """All accepting terminal coefficients c, without a time cutoff."""
    W = 1 << m
    assert 0 < I < W and I % 2 == 0
    if g % 2:
        return set(), 0
    K = max(abs(a), abs(b), abs(g))
    start = (I//2, -g//2, 1)  # compulsory initial 00
    todo, seen = deque([start]), {start}
    terminal = set()
    while todo:
        N,k,mask = todo.popleft()
        if N == 0 and mask == 7:
            terminal.add(-k)
        d = N % 2
        for e in (0, 1):
            if d and e:
                continue
            numerator = k+a*e+b*d
            if numerator % 2:
                continue
            kp = numerator//2
            assert abs(kp) <= K
            state = (N//2+(W//2)*e, kp, mask | (1 << ROWS.index((d,e))))
            if state not in seen:
                seen.add(state)
                todo.append(state)
    assert len(seen) <= 8*W*(2*K+1)
    return terminal, len(seen)


def exact_word(a, b, c, g, I, m, t):
    """Read-only integer projection; each accepting result has all positive ports."""
    assert a == 0 and b != 0
    W,q = 1 << m, 1 << t
    numerator = g-c*q
    if numerator % b:
        return None
    D = numerator//b
    if not (0 < I < W and 0 < D < q and D % W == I):
        return None
    A = D//W
    if not A or A % 2 or D & A:
        return None
    F0 = q-1-D-A
    assert F0 > 0 and F0 % 2 == 1 and D % 2 == 0
    assert all(v > 0 for v in (I//2,W-I,q//W,F0,A,D))
    assert q % W == 0 and D == I+W*A and b*D+c*q == g
    N,k = I,-g
    for j in range(t):
        d,e = (D >> j) & 1,(A >> j) & 1
        assert (d,e) in ROWS and d == N % 2
        numerator = k+b*d
        assert numerator % 2 == 0
        k = numerator//2
        N = N//2+(W//2)*e
    assert N == 0 and k == -c
    return dict(m=m,t=t,W=W,q=q,I=I,D=D,A=A,F0=F0)


def odd_orbit(B, G):
    assert B % 2
    states,bits,seen = [],[],{}
    k = -G
    K = max(abs(B),abs(G))
    while k not in seen:
        assert abs(k) <= K
        seen[k] = len(states)
        states.append(k)
        d = k % 2
        bits.append(d)
        k = (k+B*d)//2
    mu,p = seen[k],len(states)-seen[k]
    assert mu+p <= 2*K+1
    return mu,p,states,bits


def bounds(b, g, I):
    assert b != 0
    nu = (abs(b) & -abs(b)).bit_length()-1
    if g % (1 << nu):
        return dict(nu=nu,M=nu-1,short_only=True)
    B,G = b//(1 << nu),g//(1 << nu)
    mu,p,states,bits = odd_orbit(B,G)
    return dict(nu=nu,M=max(I.bit_length(),mu)+p+nu,short_only=False,
                B=B,G=G,mu=mu,p=p,states=states,bits=bits)


def bounded_at_width(b, c, g, I, m, info=None):
    info = bounds(b,g,I) if info is None else info
    limit = info['nu']-1 if info['short_only'] else m+info['mu']+2*info['p']+info['nu']
    for t in range(m+1,limit+1):
        word = exact_word(0,b,c,g,I,m,t)
        if word is not None:
            return word
    return None


def read_only_decide(b, c, g, x):
    I = 2*x
    info = bounds(b,g,I)
    for m in range(I.bit_length(),info['M']+1):
        word = bounded_at_width(b,c,g,I,m,info)
        if word is not None:
            return word
    return None


def cone_distance(b,c):
    return max(min(0,b)+c,-c-max(0,b),0)


def generated_trace(rng,m):
    """Generate a physical path first; coefficients are chosen only afterwards."""
    W = 1 << m
    I = 2*rng.randrange(1,W//2)
    N,rows = I,[]
    for j in range(rng.randrange(m+1,3*m+2)):
        d = N % 2
        e = rng.randrange(2) if j and not d else 0
        rows.append((d,e))
        N = N//2+(W//2)*e
    # If necessary, drain and then create one nonzero append.
    if not any(e for d,e in rows):
        for _ in range(m):
            rows.append((N % 2,0))
            N //= 2
        rows.append((0,1))
        N = W//2
    for _ in range(m):
        rows.append((N % 2,0))
        N //= 2
    assert N == 0 and set(rows) == set(ROWS)
    D = sum(d << j for j,(d,e) in enumerate(rows))
    A = sum(e << j for j,(d,e) in enumerate(rows))
    q = 1 << len(rows)
    assert D == I+W*A and not D & A
    return I,D,A,q,len(rows)


def check():
    rng = random.Random(20260930)
    cone_cases = cone_graphs = cone_empty = cone_states = 0
    for _ in range(240):
        a,b,g = [rng.randrange(-8,9) for _ in range(3)]
        K = max(abs(a),abs(b),abs(g))
        m = rng.randrange(2,8)
        W = 1 << m
        I = 2*rng.randrange(1,W//2)
        accepted,visited = queue_graph(a,b,g,I,m)
        cone_graphs += 1
        cone_states += visited
        for c in range(-K-2,K+3):
            delta = cone_distance(b,c)
            if delta:
                cone_cases += 1
                if delta*W > K:
                    assert c not in accepted
                    cone_empty += 1
    comparisons = graphs = visited_total = beyond_width = 0
    accepted_words = 0
    full_decision_comparisons = 0
    for _ in range(320):
        b = rng.choice([j for j in range(-12,13) if j])
        g = rng.randrange(-12,13)
        x = rng.randrange(1,17)
        I = 2*x
        info = bounds(b,g,I)
        K = max(abs(b),abs(g))
        finite_graph_union = set()
        complete_width_check = info['M'] <= 9
        for m in range(I.bit_length(),min(info['M']+2,9)+1):
            accepted,visited = queue_graph(0,b,g,I,m)
            finite_graph_union.update(accepted)
            graphs += 1
            visited_total += visited
            if m > info['M']:
                beyond_width += 1
            for c in range(-K-1,K+2):
                word = bounded_at_width(b,c,g,I,m,info)
                assert (word is not None) == (c in accepted)
                comparisons += 1
                accepted_words += word is not None
                if m > info['M'] and word is not None:
                    # A wide witness may exist, but the theorem supplies a
                    # potentially different witness inside the width cutoff.
                    assert read_only_decide(b,c,g,x) is not None
        if complete_width_check:
            for c in range(-K-1,K+2):
                assert (read_only_decide(b,c,g,x) is not None) == (c in finite_graph_union)
                full_decision_comparisons += 1
    constructed_graphs = constructed_states = constructed_compressions = 0
    for _ in range(240):
        m = rng.randrange(2,7)
        I,D,A,q,t = generated_trace(rng,m)
        b = rng.choice([j for j in range(-12,13) if j])
        c = rng.choice([j for j in range(-6,7) if j])
        g = b*D+c*q
        assert exact_word(0,b,c,g,I,m,t) is not None
        accepted,visited = queue_graph(0,b,g,I,m)
        assert c in accepted
        replacement = bounded_at_width(b,c,g,I,m)
        assert replacement is not None
        global_replacement = read_only_decide(b,c,g,I//2)
        assert global_replacement is not None
        info = bounds(b,g,I)
        assert global_replacement['m'] <= info['M']
        constructed_graphs += 1
        constructed_states += visited
        constructed_compressions += replacement['t'] < t
    # A valid rational-stream equation whose row11 prevents a FIFO witness.
    forbidden = dict(b=3,c=-2,g=-2,I=2,m=2,t=4,D=10,A=2)
    assert forbidden['b']*forbidden['D']+forbidden['c']*(1 << forbidden['t']) == forbidden['g']
    assert forbidden['D'] & forbidden['A']
    assert exact_word(0,3,-2,-2,2,2,4) is None
    # Genuine nonabsorbing odd-B example; its q cannot be doubled for free.
    ordinary = exact_word(0,5,-3,-4,12,5,7)
    assert ordinary is not None
    assert 5*ordinary['D']-3*(2*ordinary['q']) != -4
    # The eventually zero low stream: arbitrarily wide witnesses compress.
    wide = exact_word(0,4,-1,8,2,12,16)
    compressed = exact_word(0,4,-1,8,2,5,9)
    assert wide is not None and compressed is not None
    assert bounds(4,8,2)['M'] == 5
    assert read_only_decide(4,-1,8,1) is not None
    # nu=6 and t=5: g is not divisible by2^nu, but short cases matter.
    short = exact_word(0,64,1,1184,2,2,5)
    assert short is not None and bounds(64,1184,2)['short_only']
    assert read_only_decide(64,1,1184,1) is not None
    return dict(
        status='PASS_BINARY_NONABSORBING_CONE_AND_READ_ONLY',
        proof='binary_nonabsorbing_cone_and_read_only.md',
        arithmetic_dependency='native_binary_three_row_fifo58.md',
        cone=dict(coefficient_checks=cone_cases,full_graphs=cone_graphs,
                  graph_states=cone_states,excluded_above_bound=cone_empty),
        read_only=dict(full_graphs=graphs,graph_states=visited_total,
                       endpoint_comparisons=comparisons,accepting_word_checks=accepted_words,
                       graphs_beyond_width_cutoff=beyond_width,
                       full_decider_comparisons=full_decision_comparisons,
                       constructed_accepting_graphs=constructed_graphs,
                       constructed_graph_states=constructed_states,
                       constructed_shortened_histories=constructed_compressions),
        guard_regression=forbidden,
        examples=dict(nonabsorbing_odd_read=ordinary,eventually_zero_wide=wide,
                      eventually_zero_compressed=compressed,short_duration=short),
        ledgers=dict(general_component=dict(operations=63,multiplications=33,additions=30),
                     read_only_component=dict(operations=61,multiplications=32,additions=29,
                                              positive_existential_coordinates=26,equations=18)),
        scope='Parametric cone obstruction and all-a=0 decidability; the general a!=0 interior is not decided here, and binary_fixed_idle_controller.md classifies one boundary.',
        established_complete_bound=75,
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = check()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result
    print(json.dumps(result,indent=2))
