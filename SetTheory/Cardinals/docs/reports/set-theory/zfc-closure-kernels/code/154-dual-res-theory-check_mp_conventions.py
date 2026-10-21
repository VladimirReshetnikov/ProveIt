#!/usr/bin/env python3
"""Symbolic stack calculations for alternative MP return conventions.

This is a regression check of the block interfaces, not a source/TM proof.
Opaque stack tails make accidental over-popping fail rather than look benign.
BUILD is an explicit induction-hypothesis placeholder, not a machine command.
"""
from itertools import product
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Run without Python optimization: assertions are checks")


def add(a, b):
    if a == 0:
        return b
    if b == 0:
        return a
    return a + b if isinstance(a, int) and isinstance(b, int) else ('+', a, b)


def I(a, b):
    return 0 if a == b == 0 else ('I', a, b)


def Q(a, b):
    return ('Q', a, b)


def R(a, b):
    return ('R', a, b)


def E(a, b):
    return ('E', a, b)


def N(a):
    return I(a, 1)


def Ex(a, b):
    return N(Q(a, N(b)))


def P(a, b):
    return 0 if a == b == 0 else ('P', a, b)


def unP(w):
    if w == 0:
        return 0, 0
    assert isinstance(w, tuple) and w[0] == 'P', ('opaque_tail_was_popped', w)
    return w[1], w[2]


def rows(a, b, c, u):
    return [
        Ex(a, E(a, b)),
        I(Q(a, I(b, c)), I(Q(a, b), Q(a, c))),
        I(E(a, b), I(R(c, a), R(c, b))),
        I(Q(a, Q(b, c)), Q(b, Q(a, c))),
        I(E(c, a), I(R(c, b), R(a, b))),
        I(Ex(a, Q(a, c)), c),
        I(E(c, a), I(E(c, b), Q(R(a, b), E(a, b)))),
        I(I(I(c, u), a), I(I(a, c), I(b, c))),
    ]


def gate(a, b, c):
    return 0 if c in (a, b) else ('Bundle', a, b, c)


def ax_stack(a, h, b, c, u, t, w):
    for x in reversed(rows(a, b, c, u) + [Q(a, h), t]):
        w = P(x, w)
    return w


DROP = ('DROP',)
NIP = ('NIP',)


def xstep(kind, command, q):
    t, w, d, h = q
    op = command[0]
    if op == 'BUILD':
        assert d == h == 0
        return command[1], w, 0, 0
    if op == 'MP':
        D = add(d, command[1])
        if I(t, D) != h:
            return 0, w, D, 0
        if kind == 'copy':
            return D, w, D, 0
        if kind == 'move':
            return D, w, 0, 0
        if kind == 'cache':
            return 0, w, 0, D
        raise AssertionError(kind)
    if op == 'DROP':
        return h, P(t, w), d, h
    if op == 'NIP':
        if h == 1:
            return None
        h1, w1 = unP(w)
        return t, w1, d, h1
    if op == 'AX':
        _, c, x, y, u = command
        a, b = add(d, x), add(h, y)
        return gate(a, b, c), ax_stack(a, h, b, c, u, t, w), 0, 0
    raise AssertionError(command)


def execute(kind, commands, q):
    for command in commands:
        q = xstep(kind, command, q)
        if q is None:
            return None
    return q


def leaf(j, a, b, c, u):
    return [('MP', 0), ('AX', c, a, b, u)] + [NIP]*j + [DROP] + [NIP]*(11-j)


def main():
    counts = {k: 0 for k in ('discard', 'axiom_leaves', 'bundle', 'gen', 'mp', 'whole_program')}
    Tvalues = [0, 1, ('Current', 'T')]
    Wvalues = [0, ('Tail', 'w'), P(1, ('Tail', 'w'))]
    Vvalues = [0, 1, ('Formula', 'A'), I(1, 0), Q(0, 0)]
    a, b, c, u = [('Parameter', s) for s in 'abcu']
    for kind, T, w in product(('copy', 'move', 'cache'), Tvalues, Wvalues):
        q0 = (T, w, 0, 0)
        assert execute(kind, [('MP', 0)], q0) == (0, w, 0, 0)
        counts['discard'] += 1
        for j in range(1, 9):
            assert execute(kind, leaf(j, a, b, c, u), q0) == (rows(a,b,c,u)[j-1], w, 0, 0)
            counts['axiom_leaves'] += 1
        L = [('MP', 0), ('AX', c, a, b, 0)] + [NIP]*10
        assert execute(kind, L, q0) == (gate(a,b,c), w, 0, 0)
        counts['bundle'] += 1
        for X in Vvalues:
            # This is exactly the unchanged GEN stack template.
            L = [('BUILD', X), DROP, NIP, ('AX', a, a, 0, 0)] + [NIP]*9 + [DROP, NIP, NIP]
            out = execute(kind, L, q0)
            assert out is None or out == (Q(a,X), w, 0, 0), (kind,'gen',X,out)
            counts['gen'] += 1
        for A, B in product(Vvalues, repeat=2):
            L = [('BUILD', A), DROP, ('BUILD', I(A,B)), NIP, DROP, NIP, ('MP', B)]
            if kind == 'copy':
                L += [('AX', B, 0, 0, 0)] + [NIP]*10 + [DROP, NIP]
            elif kind == 'cache':
                L += [DROP, NIP]
            out = execute(kind, L, q0)
            assert out is None or out == (B,w,0,0), (kind,'mp',A,B,out)
            counts['mp'] += 1
        # START resets arbitrary retained d,h; BUILD(1) is the induction
        # hypothesis for a contradiction block, not an assumed contradiction.
        for d, h in product(Vvalues, repeat=2):
            L = [('AX', 0, 1, 1, 0), ('BUILD', 1), DROP, NIP, NIP]
            assert execute(kind, L, (T,w,d,h)) is None
            counts['whole_program'] += 1
    result = {
        'status': 'SYMBOLIC_BLOCK_CONTRACTS_PASS',
        'conventions': ['no_push_copy','no_push_move','no_push_cache'],
        'checks': counts,
        'total': sum(counts.values()),
        'native_zero_alias': 'I(0,0)=0 and P(0,0)=0 explicitly respected',
        'opaque_stack_tails': True,
        'scope': 'Symbolic block-interface regression; BUILD is an induction-hypothesis placeholder. Not a source or TM certification.',
    }
    target = Path(__file__).with_name('mp_conventions_receipt.json')
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
