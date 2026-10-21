#!/usr/bin/env python3
"""Exact stack-equation corroboration for the stride-two command compiler.

The all-natural proofs are in proof.md.  AX rows are opaque constructor-safe
tokens except for the independently checked rho6/rho8 non-detachment lemma.
This is not a binary-runtime certificate or a proof-assistant kernel check.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from math import isqrt
import argparse
import json


@dataclass(frozen=True)
class Term:
    op: str
    args: tuple = ()


@dataclass(frozen=True)
class Stack:
    head: object
    tail: object


class Halt(Exception):
    pass


DIRECT = False


def V(name):
    return Term('variable', (name,))


def I(a, b):
    return 0 if a == b == 0 else Term('I', (a, b))


def Q(i, a):
    return Term('Q', (i, a))


def add(a, b):
    if a == 0: return b
    if b == 0: return a
    if isinstance(a, int) and isinstance(b, int): return a + b
    return Term('add', (a, b))


def row(j, a, b, c, u):
    return Term('row' + str(j), (a, b, c, u))


def gate(a, b, c):
    return 0 if c == a or c == b else Term('gate', (a, b, c))


def ax(st, c=0, x=0, y=0):
    t, w, d, h = st
    a, b = add(d, x), add(h, y)
    entries = [row(j, a, b, c, d) for j in range(1, 9)] + [Q(d, h), t]
    for value in reversed(entries): w = Stack(value, w)
    return gate(a, b, c), w, 0, 0


def shift2(st):
    t, w, d, h = st
    if h == 1 or (t == 1 and not DIRECT): raise Halt()
    assert isinstance(w, Stack), ('protected suffix inspected', w)
    if w.head == 1: raise Halt()
    assert isinstance(w.tail, Stack), ('protected suffix inspected', w.tail)
    return h, w.tail.tail, d, w.tail.head


def mismatch(t, y, h):
    target = I(t, y)
    if h == 0:
        # All calls here have a visibly positive target, except exact success.
        assert target != 0
        return True
    if isinstance(h, Term) and h.op == 'Q': return True
    if (y == 0 and isinstance(t, Term) and t.op == 'row6'
            and isinstance(h, Term) and h.op == 'row8'):
        assert t.args == h.args
        # Uses the all-natural lemma proved in proof.md and independently
        # corroborated numerically in check_constructor_lemma below.
        return True
    raise AssertionError(('unproved comparison', target, h))


def mp(st, x):
    t, w, d, h = st
    y = add(d, x)
    if I(t, y) == h: return y, Stack(0, w), y, 0
    assert mismatch(t, y, h)
    return 0, w, y, 0


S = ('S2',)
M = lambda x: ('MP', x)
A = lambda c=0, x=0, y=0: ('AX', c, x, y)
H = [A()] + [S] * 6
PUSH = [A()] + [S] * 4 + [M(0), M(0), S, M(0)]
DISCARD = [M(1), A(1)] + H * 5
J = lambda u: [] if u == 0 else [M(u)]


def run(st, block):
    for k in block:
        if k[0] == 'S2': st = shift2(st)
        elif k[0] == 'MP': st = mp(st, k[1])
        else: st = ax(st, *k[1:])
    return st


def select_row(j, a, b, c, u=0):
    assert 1 <= j <= 9 and isinstance(a, int) and 0 <= u <= a
    block = DISCARD[:]
    if j % 2: block += [M(0)]  # one zero below the future AX packet
    block += J(u) + [A(c, a-u, b)]
    if j % 2:
        # Exactly one new zero above the packet; a positive gate requires
        # one preliminary failing MP(0) to clear the current value.
        block += [M(0)] if gate(a, b, c) == 0 else [M(0), M(0)]
        block += [S] * ((j + 3) // 2) + H * ((9-j) // 2)
    else:
        block += [S] * (j // 2 + 1) + H * ((8-j) // 2)
    return block


def P(a, b): return (a+b)*(a+b+1)//2+b
def numI(a, b): return 4*P(a, b)
def numQ(i, a): return 4*P(i, a)+2
def unpair(n):
    s = (isqrt(8*n+1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b


def check_constructor_lemma():
    count = 0
    for a in range(12):
        for b in range(12):
            for c in range(12):
                for u in range(a+1):
                    r6 = numI(numI(numQ(a, numI(numQ(a, b), 1)), 1), b)
                    r8 = numI(numI(numI(c, u), a), numI(numI(a, c), numI(b, c)))
                    assert r6 > 0 and numI(r6, 0) != r8
                    if r8 == 0: assert a == b == c == u == 0
                    count += 1
    return count


def main():
    global DIRECT
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('checks.json'))
    ap.add_argument('--direct', action='store_true',help='Use the short clear/load/NIP/NIP command without the old-top guard')
    args = ap.parse_args()
    DIRECT=args.direct
    records = []
    def check(name, st, block, expected, halt_policy='allowed'):
        assert halt_policy in ('allowed','forbidden','required')
        try:
            got = run(st, block)
            assert halt_policy != 'required', (name, 'required halt did not occur')
            assert got == expected, (name, got, expected)
            status = 'EXACT_RETURN'
        except Halt:
            assert halt_policy != 'forbidden', (name, 'unexpected halt')
            status = 'PERMITTED_EARLY_HALT'
        records.append({'name': name, 'commands': len(block), 'status': status,
                        'halt_policy':halt_policy})
    tail, t, x, y = V('protected tail'), V('top'), V('first head'), V('second head')
    check('H2 arbitrary', (t, Stack(x, Stack(y, tail)), V('d'), V('h')), H, (t, tail, 0, y))
    check('H2 tests top1', (1, Stack(x, Stack(y, tail)), 0, 0), H, None,'required')
    check('H2 tests first1', (t, Stack(1, Stack(y, tail)), 0, 0), H, None,'required')
    check('PUSH arbitrary', (t, tail, V('d'), V('h')), PUSH, (0, Stack(t, tail), 0, 0),'forbidden')
    check('PUSH cache1', (t, tail, 4, 1), PUSH, (0, Stack(t, tail), 0, 0),'forbidden')
    check('PUSH top1', (1, tail, 4, 1), PUSH, (0, Stack(1, tail), 0, 0),'forbidden')
    for tt in [t, 0, 1, Q(0, t)]:
        check('DISCARD '+str(tt), (tt, tail, 0, 0), DISCARD, (0, tail, 0, 0),'forbidden')
    for a, b, c, u in [(0,0,0,0),(2,1,0,0),(2,1,3,1),(2,3,4,2),(3,3,3,1)]:
        for j in range(1,10):
            target = row(j,a,b,c,u) if j<9 else Q(u,0)
            check(f'row{j} {a,b,c,u}', (t,tail,0,0), select_row(j,a,b,c,u), (target,tail,0,0))
        check('bundle '+str((a,b,c)), (t,tail,0,0), DISCARD+[A(c,a,b)]+H*5,
              (gate(a,b,c),tail,0,0))
    for i in [0,1,3]:
        for X in [0,1,I(V('p'),V('q')),Q(0,V('p'))]:
            # Establish an extra zero below the protected premise evaluation.
            st = run((t,tail,0,0), DISCARD+[M(0)])
            assert st == (0,Stack(0,tail),0,0)
            # HOLE B_X: exact inductive compiler contract on the padded stack.
            st = X, st[1], 0, 0
            block = PUSH+[M(0)]+J(i)+[S,A(i),M(0)]+[S]*6
            check(f'GEN {i} {X}', st, block, (Q(i,X),tail,0,0))
    for a,b in [(0,0),(0,1),(1,0),(1,1),(V('a'),V('b')),(Q(0,t),I(t,x))]:
        st = run((t,tail,0,0), DISCARD+[M(0)])
        # HOLE B_I(a,b), preserving padded suffix.
        st = I(a,b), st[1], 0, 0
        st = run(st, PUSH+[M(0)])
        # HOLE B_a, preserving the stored major and its zero padding.
        st = a, st[1], 0, 0
        block = PUSH+[M(0),S,S,M(b)]+H
        check(f'MP {a,b}', st, block, (b,tail,0,0))
    check('terminal1', (1,tail,0,0), H, None,'required')
    # Independent conservative credit recurrence for the actual MP0/S2=1 tags.
    count=100000
    balances=[]; minima=[]; cumulative=[0]; low=0
    for n in range(count):
        tag, rest = unpair(n)
        if tag==0: delta=0; rest=unpair(rest)[1]
        elif tag==1: delta=-2
        else: delta=10; rest=unpair(unpair(rest)[1])[1]
        b=delta+(balances[rest-1] if rest else 0)
        m=min(0,delta+(minima[rest-1] if rest else 0))
        low=min(low,cumulative[-1]+m)
        balances.append(b);minima.append(m);cumulative.append(cumulative[-1]+b)
        assert cumulative[-1]+2*(n+1)>=0
    assert low==-2
    diags=0
    for s in range(2,500):
        begin=s*(s+1)//2;end=(s+1)*(s+2)//2
        if end>count:break
        relative=0
        for n in range(begin,end):
            assert relative+minima[n]>=0
            relative+=balances[n]
        assert relative>=4*s-8
        diags+=1
    report={'status':'PASS_STACK_EQUATIONS_AND_FINITE_CREDIT',
            'command':'direct clear/load/NIP/NIP' if DIRECT else 'composite DROP/NIP/NIP/NIP',
            'interface_cases':len(records),'cases':records,
            'rho6_rho8_literal_numeric_cases':check_constructor_lemma(),
            'credit_candidate_count':count,'complete_diagonals':diags,
            'minimum_conservative_prefix_balance':low,'required_credit_at_N1':2,
            'scope':'Symbolic stack interfaces use explicit row safety and the written rho6/rho8 lemma; HOLE steps are inductive contracts. Finite credit checks corroborate, not replace, the all-natural diagonal proof. No physical machine proof.'}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cases'},indent=2))


if __name__=='__main__':main()
