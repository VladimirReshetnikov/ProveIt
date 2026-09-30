#!/usr/bin/env python3
"""Exact scalar-orbit compression, retaining every physical binary guard."""
import argparse
from collections import deque
import json
from math import gcd
from pathlib import Path
import random

ROWS = ((0,0),(0,1),(1,0))


def core_step(w,L):
    return (w+L*(w % 2))//2


def scalar_structure(a,b,g,I,m):
    W = 1 << m
    C = a+b*W
    assert a % 2 and C % 2 and 0 < I < W and I % 2 == 0
    sigma,L = (1 if C > 0 else -1),abs(C)
    w = sigma*(b*I-g)
    initial = w
    distance = max(-w,w-L,0)
    mu = 0
    while not 0 <= w <= L:
        before = max(-w,w-L,0)
        w = core_step(w,L)
        assert max(-w,w-L,0) <= before//2
        mu += 1
    assert mu <= distance.bit_length()
    core = w
    if core in (0,L):
        modulus,p = 1,1
    else:
        modulus = L//gcd(core,L)
        residue,p = 2 % modulus,1
        while residue != 1:
            residue = 2*residue % modulus
            p += 1
        assert p <= L-1
    visited = set()
    for _ in range(p):
        assert w not in visited and 0 <= w <= L
        visited.add(w)
        w = core_step(w,L)
    assert w == core
    uniform = None
    if b:
        signb = 1 if b > 0 else -1
        B,an,gn = abs(b),signb*a,signb*g
        if B*W+an > 0:
            E = max(0,gn-2*B,-gn-an-2*B)
            uniform = E.bit_length()
            assert mu <= uniform
    return dict(C=C,L=L,sigma=sigma,initial=initial,core=core,mu=mu,p=p,
                order_modulus=modulus,entry_bound=distance.bit_length(),
                uniform_entry_bound=uniform)


def scalar_acceptances(a,b,g,I,m):
    data = scalar_structure(a,b,g,I,m)
    W,K = 1 << m,max(abs(a),abs(b),abs(g))
    limit = data['mu']+m+2*data['p']
    z,N,mask,A,D = b*I-g,I,0,0,0
    accepted = {}
    failure = None
    for j in range(limit):
        d,e = N % 2,z % 2
        if (j == 0 and e) or d*e:
            failure = j
            break
        assert abs(z-b*N) <= K
        D += d << j
        A += e << j
        mask |= 1 << ROWS.index((d,e))
        z = (z+data['C']*e)//2
        N = N//2+(W//2)*e
        assert abs(z-b*N) <= K
        t,q = j+1,1 << (j+1)
        assert D == I+W*A-q*N
        if N == 0 and mask == 7:
            c = -z
            F0 = q-1-A-D
            assert t > m and not A & D and A % 2 == D % 2 == 0
            assert all(v > 0 for v in (I//2,W-I,q//W,F0,A,D))
            assert a*A+b*D+c*q == g
            assert W <= A+F0
            accepted.setdefault(c,dict(t=t,A=A,D=D,q=q,F0=F0))
            if data['core'] != 0 and data['p'] <= m:
                assert m < t < data['mu']+m
            if data['core'] == 0 and c != 0:
                assert t < data['mu']
    return accepted,data,failure


def product_graph(a,b,g,I,m):
    """Independent finite queue/carry graph, including row-occurrence flags."""
    W = 1 << m
    K = max(abs(a),abs(b),abs(g))
    if g % 2:
        return set(),0
    start = (I//2,-g//2,1)
    todo,seen = deque([start]),{start}
    accepted = set()
    while todo:
        N,k,mask = todo.popleft()
        if N == 0 and mask == 7:
            accepted.add(-k)
        d = N % 2
        for e in (0,1):
            if d*e or (k+a*e+b*d) % 2:
                continue
            kp = (k+a*e+b*d)//2
            assert abs(kp) <= K
            nxt = (N//2+(W//2)*e,kp,mask | (1 << ROWS.index((d,e))))
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    assert len(seen) <= 8*W*(2*K+1)
    return accepted,len(seen)


def physical_trace(rng,m):
    W = 1 << m
    I = 2*rng.randrange(1,W//2)
    N,rows = I,[]
    for j in range(rng.randrange(m+2,3*m+2)):
        d = N % 2
        e = rng.randrange(2) if j and not d else 0
        rows.append((d,e))
        N = N//2+(W//2)*e
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
    F0 = q-1-A-D
    assert D == I+W*A and not A & D and F0 > 0
    assert W <= A+F0
    return I,A,D,q


def check():
    rng = random.Random(20261001)
    graph_cases = graph_states = order_checks = 0
    transients_below = transients_above = 0
    uniform_checks = short_period_checks = 0
    accepted_endpoints = constructed = 0
    max_mu = max_p = 0
    for i in range(1000):
        m = rng.randrange(2,9)
        W = 1 << m
        a = rng.choice([j for j in range(-13,14) if j % 2])
        b = rng.randrange(-9,10)
        if i < 700:
            I,g = 2*rng.randrange(1,W//2),rng.randrange(-40,41)
            required = None
        else:
            I,A,D,q = physical_trace(rng,m)
            c = rng.choice([j for j in range(-9,10) if j])
            g = a*A+b*D+c*q
            required = c
            constructed += 1
        actual,data,_ = scalar_acceptances(a,b,g,I,m)
        expected,visited = product_graph(a,b,g,I,m)
        assert set(actual) == expected,(a,b,g,I,m,data,actual,expected)
        if required is not None:
            assert required in actual
        graph_cases += 1
        graph_states += visited
        order_checks += data['order_modulus'] != 1
        transients_below += data['initial'] < 0
        transients_above += data['initial'] > data['L']
        uniform_checks += data['uniform_entry_bound'] is not None
        short_period_checks += data['p'] <= m
        accepted_endpoints += len(actual)
        max_mu,max_p = max(max_mu,data['mu']),max(max_p,data['p'])
    boundary_cases = boundary_acceptances = boundary_exclusions = 0
    for _ in range(700):
        b = rng.choice([j for j in range(-7,8) if j])
        signb,B = (1 if b > 0 else -1),abs(b)
        an = rng.randrange(-10,B)
        a = signb*an
        m = rng.randrange(2,8)
        W = 1 << m
        I = 2*rng.randrange(1,W//2)
        g = rng.randrange(-80,81)
        accepted,_ = product_graph(a,b,g,I,m)
        R,s = -signb*g-B,min(B-an,B)
        limit = R//s
        if -b in accepted:
            assert R > 0 and W <= limit
            boundary_acceptances += 1
        if W > limit:
            assert -b not in accepted
            boundary_exclusions += 1
        boundary_cases += 1
    # Positive boundary fixtures chosen after generating the physical trace.
    for _ in range(160):
        m = rng.randrange(2,7)
        I,A,D,q = physical_trace(rng,m)
        b = rng.choice([j for j in range(-7,8) if j])
        signb,B = (1 if b > 0 else -1),abs(b)
        an = rng.randrange(-8,B)
        a,c = signb*an,-b
        g = a*A+b*D+c*q
        R,s = -signb*g-B,min(B-an,B)
        assert (1 << m) <= R//s
        accepted,_ = product_graph(a,b,g,I,m)
        assert c in accepted
        boundary_cases += 1
        boundary_acceptances += 1
    # A false unguarded endpoint: exact equation, wrong physical row11.
    z,appends = 6,[]
    for _ in range(4):
        e = z % 2
        appends.append(e)
        z = (z+13*e)//2
    assert appends == [0,1,0,0] and z == 2
    assert 1*2+3*10-2*16 == 0 and 2 & 10
    guarded,_,failure = scalar_acceptances(1,3,0,2,2)
    assert failure == 1 and not guarded
    # A true nonabsorbing interior history, which cannot be padded with00.
    valid,valid_data,_ = scalar_acceptances(1,3,-6,2,2)
    assert -2 in valid and valid[-2]['t'] == 5
    word = valid[-2]
    assert word['A']+3*word['D']-2*(2*word['q']) != -6
    return dict(
        status='PASS_BINARY_ODD_CONTROLLER_ORBIT',
        proof='binary_odd_controller_orbit.md',
        arithmetic_dependency='native_binary_three_row_fifo58.md',
        orbit=dict(full_graph_comparisons=graph_cases,graph_states=graph_states,
                   multiplicative_order_checks=order_checks,below_core_transients=transients_below,
                   above_core_transients=transients_above,uniform_transient_checks=uniform_checks,
                   short_period_checks=short_period_checks,constructed_accepting_runs=constructed,
                   accepting_endpoints=accepted_endpoints,max_observed_preperiod=max_mu,
                   max_observed_period=max_p),
        boundary=dict(full_graph_cases=boundary_cases,accepting_cases=boundary_acceptances,
                      excluded_above_width_bound=boundary_exclusions,
                      condition='b!=0,c=-b,a/b<1',width_bound='floor((-sign(b)*g-abs(b))/min(abs(b)-sign(b)*a,abs(b)))'),
        false_unguarded_endpoint=dict(a=1,b=3,c=-2,g=0,I=2,W=4,t=4,A=2,D=10,
                                      first_forbidden_row=1),
        true_nonabsorbing_example=dict(a=1,b=3,c=-2,g=-6,I=2,W=4,
                                       word=word,structure=valid_data),
        paid_component=dict(operations=63,multiplications=33,additions=30,
                            equations=18,positive_existential_coordinates=26),
        scope='Exact fixed-width odd-a orbit and finite-language c=-b,a/b<1 boundary; no decision for all unbounded widths.',
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
