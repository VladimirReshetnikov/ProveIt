#!/usr/bin/env python3
"""Exact finite examples for the observation compiler and FTA budgets.

This program checks implementations and arithmetic examples; it is not an
iPRA proof checker and does not execute the enormous full FTA descent.
The generic locality theorem is proved separately in FiniteObservation.lean.
"""
from fractions import Fraction as Q
from functools import lru_cache
import json


def backwards_budgets(use, stages, final_horizon):
    """use(s,h) is a proved monotone verification demand, including queries."""
    hs = [final_horizon] * (stages + 1)
    for s in range(stages - 1, -1, -1):
        hs[s] = use(s, hs[s + 1])
        assert hs[s] >= hs[s + 1]
    return hs


def compile_tables(base, body, use, stages, horizon):
    hs = backwards_budgets(use, stages, horizon)
    row = [base(p) for p in range(hs[0] + 1)]
    visited = len(row)
    for s in range(stages):
        row = [body(s, p, row) for p in range(hs[s + 1] + 1)]
        visited += len(row)
    return row, hs, visited


def check_compiler():
    equalities = compatibility = observations = 0
    examples = []
    for mode in range(3):
        if mode == 0:
            use = lambda s, h: h + s + 1
            body = lambda s, p, row: row[p] + row[p + s + 1]
        elif mode == 1:
            use = lambda s, h: 2 * h + 1
            body = lambda s, p, row: sum(row[:2 * p + 2]) + s
        else:
            # A verification budget deliberately larger than the actual reads.
            use = lambda s, h: h + 4
            body = lambda s, p, row: row[p + 1] * row[p] + 1
        base = lambda p: p % 5 + 1

        @lru_cache(None)
        def semantic(stage, p):
            if stage == 0:
                return base(p)
            prev = [semantic(stage - 1, j) for j in range(use(stage - 1, p) + 1)]
            return body(stage - 1, p, prev)

        for stages in range(7):
            for horizon in range(7):
                row, hs, visited = compile_tables(base, body, use, stages, horizon)
                observations += visited
                for p, value in enumerate(row):
                    assert value == semantic(stages, p)
                    equalities += 1
                larger, _, _ = compile_tables(base, body, use, stages, horizon + 1)
                assert row == larger[:horizon + 1]
                compatibility += 1
                if stages == 4 and horizon == 3:
                    examples.append({'mode': mode, 'horizons': hs,
                                     'output': row, 'observations': visited})
    return {'nested_equalities': equalities,
            'prefix_compatibility_checks': compatibility,
            'observations_in_runs': observations,
            'examples': examples}


def fta_constants(n, M):
    assert n >= 1 and M >= 2
    B = M + 2
    D = 2**n * 4**(2*n*n)
    K = 8*n*D
    R = B*K + 1
    L = 2 + (16*D*(n+1)*R**n).bit_length()
    H = (B*K).bit_length()
    A = 2*R + 1
    E = 4*(n+1)**2*(M+1)*(A+1)**(n+1)
    shift = (4*E).bit_length()
    Mplus = 2+(n+1)*(M+1)*(A+1)**n
    Dplus = 4*(n+1)*(Mplus+1)*(A+1)
    return dict(n=n, M=M, B=B, D=D, K=K, R=R, L=L, H=H,
                A=A, E=E, shift=shift, Mplus=Mplus, Dplus=Dplus)


def verification_use(c, h):
    return c['L'] + c['K'] * (h+c['shift']+2+c['H']+2)


def check_fta_budgets():
    rows = []
    for d in range(1, 5):
        caps = [2]
        cs = []
        for s in range(d):
            c = fta_constants(d-s, caps[-1])
            assert Q(c['E'], 2**c['shift']) < Q(1, 4)
            assert 2**c['L'] > 16*c['D']*(c['n']+1)*c['R']**c['n']
            assert 2**c['H'] > c['B']*c['K']
            caps.append(c['Mplus'])
            cs.append(c)
        G = 1+max(c['A'] for c in cs)
        W = 1+max(c['Dplus'] for c in cs)
        shift = (1+d*W*G**d).bit_length()
        assert Q(d*W*G**d, 2**shift) <= 1
        hs = backwards_budgets(lambda s, h: verification_use(cs[s], h), d, shift+4)
        rows.append({'degree': d, 'initial_cap': 2,
                     'cap_bit_lengths': [x.bit_length() for x in caps],
                     'horizon_bit_lengths': [x.bit_length() for x in hs],
                     'final_precision_shift': shift})
    return {'scope': 'budgets only; full FTA root algorithm not executed', 'cases': rows}


def check_telescoping():
    count = 0
    for n in range(8):
        factors = [Q((3*j+2) % 7 + 1, j+1) for j in range(n)]
        errors = [Q((-1)**j, 2**(j+2)) for j in range(n)]
        states = [Q(0)]*(n+1)
        states[n] = Q(3, 7)
        for j in range(n-1, -1, -1):
            states[j] = factors[j]*states[j+1]+errors[j]
        product = Q(1)
        total = Q(0)
        bound = Q(0)
        for j in range(n):
            total += product*errors[j]
            bound += abs(product)*abs(errors[j])
            product *= factors[j]
        assert states[0]-product*states[n] == total
        assert abs(total) <= bound
        count += 1
    return {'exact_chains': count}


if __name__ == '__main__':
    print(json.dumps({'status': 'all exact finite checks passed',
                      'compiler': check_compiler(),
                      'fta_budgets': check_fta_budgets(),
                      'defect_transport': check_telescoping()}, indent=2))
