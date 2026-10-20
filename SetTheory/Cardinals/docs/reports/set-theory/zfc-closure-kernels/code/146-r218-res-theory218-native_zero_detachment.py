#!/usr/bin/env python3
"""Proof-producing CD/GEN screen including the native identity I(0,0)=0.

The native implication constructor is injective, but its (0,0) pair is
code zero again. Positive constructor codes strictly exceed their
children. Unification therefore permits an occurs-check cycle only when
its complete component consists of implication nodes and can collapse
to zero. Quantification is represented by one fixed native binder.

This is a discovery tool. Positive certificates still need explicit
substitution/MP replay; a bounded failure has no consistency implication.
"""
import argparse
from functools import lru_cache
import heapq
import json
from pathlib import Path
import time

ZERO = 't'


def C(a, b):
    return ZERO if a == b == ZERO else ('C', a, b)


def Q(a):
    return ('Q', a)


@lru_cache(None)
def size(t):
    return 1 + sum(size(x) for x in t[1:]) if isinstance(t, tuple) else 1


@lru_cache(None)
def depth(t):
    return ((t[0] == 'Q') + max(map(depth, t[1:]))) if isinstance(t, tuple) else 0


@lru_cache(None)
def nvars(t):
    return max(map(nvars, t[1:])) if isinstance(t, tuple) else t + 1 if isinstance(t, int) else 0


def canonical(t):
    variables = {}

    def go(x):
        if isinstance(x, tuple):
            return C(go(x[1]), go(x[2])) if x[0] == 'C' else Q(go(x[1]))
        return variables.setdefault(x, len(variables)) if isinstance(x, int) else x
    return go(t)


def rename(t, n):
    if isinstance(t, tuple):
        return (t[0],) + tuple(rename(x, n) for x in t[1:])
    return t + n if isinstance(t, int) else t


def detach(major, minor, native_zero=True):
    if major == ZERO and native_zero:
        return ZERO if minor == ZERO else None
    if not isinstance(major, tuple) or major[0] != 'C':
        return None
    minor = rename(minor, nvars(major))
    bindings = {}

    def resolve(t):
        if isinstance(t, int) and t in bindings:
            return resolve(bindings[t])
        if isinstance(t, tuple):
            children = tuple(resolve(x) for x in t[1:])
            if t[0] == 'C' and native_zero:
                return C(*children)
            return (t[0],) + children
        return t

    def occurs(v, t):
        return any(occurs(v, x) for x in t[1:]) if isinstance(t, tuple) else t == v

    def force_zero(t):
        if t == ZERO:
            return True
        if isinstance(t, int):
            bindings[t] = ZERO
            return True
        if isinstance(t, tuple) and t[0] == 'C':
            return all(force_zero(x) for x in t[1:])
        return False

    stack = [(major[1], minor)]
    while stack:
        x, y = (resolve(t) for t in stack.pop())
        if x == y:
            continue
        if isinstance(y, int) and not isinstance(x, int):
            x, y = y, x
        if isinstance(x, int):
            if occurs(x, y):
                if not native_zero or not force_zero(y):
                    return None
                bindings[x] = ZERO
            else:
                bindings[x] = y
        elif isinstance(x, tuple) and isinstance(y, tuple) and x[0] == y[0]:
            stack.extend(zip(x[1:], y[1:]))
        elif native_zero and x == ZERO and isinstance(y, tuple) and y[0] == 'C':
            stack.extend((z, ZERO) for z in y[1:])
        elif native_zero and y == ZERO and isinstance(x, tuple) and x[0] == 'C':
            stack.extend((z, ZERO) for z in x[1:])
        else:
            return None
    return canonical(resolve(major[2]))


def subsumes(p, t):
    bindings = {}
    stack = [(p, t)]
    while stack:
        x, y = stack.pop()
        if isinstance(x, int):
            if x in bindings and bindings[x] != y:
                return False
            bindings[x] = y
        elif isinstance(x, tuple):
            if y == ZERO and x[0] == 'C':
                stack.extend((z, ZERO) for z in x[1:])
            elif isinstance(y, tuple) and x[0] == y[0]:
                stack.extend(zip(x[1:], y[1:]))
            else:
                return False
        elif x != y:
            return False
    return True


def word(t):
    if isinstance(t, tuple):
        return t[0] + ''.join(map(word, t[1:]))
    return str(t) + ',' if isinstance(t, int) else t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--basis', choices=['b_truth', 'b_aa', 'reduced', 'G'], default='b_truth')
    ap.add_argument('--extra', choices=['none', 'identity', 'explosion', 'both'], default='none')
    ap.add_argument('--no-modal', action='store_true')
    ap.add_argument('--maxsize', type=int, default=101)
    ap.add_argument('--depth', type=int, default=8)
    ap.add_argument('--steps', type=int, default=2000)
    ap.add_argument('--seconds', type=float, default=90)
    args = ap.parse_args()
    a, c, u = 0, 1, 2
    B = ZERO if args.basis == 'b_truth' else C(a, a)
    first = C(C(C(c, u), a), C(C(a, c), C(B, c)))
    if args.basis == 'reduced':
        first = C(C(C(c, u), a), C(C(a, c), c))
    if args.basis == 'G':
        first = C(C(C(a, c), a), C(u, a))
    axioms = [first, ZERO]
    if not args.no_modal:
        axioms.extend([C(Q(C(a, c)), C(Q(a), Q(c))),
                       C(C(Q(C(Q(a), 'f')), 'f'), a)])
    if args.extra in ('identity', 'both'):
        axioms.append(C(a, a))
    if args.extra in ('explosion', 'both'):
        axioms.append(C('f', a))
    targets = {'I': C(a, a), 'K': C(a, C(c, a)),
               'P': C(C(C(a, c), a), a),
               'H': C(C(a, c), C(C(c, u), C(a, u))),
               'L': C(C(C(a, c), u), C(C(u, a), C(3, a)))}
    nodes, known, pending, processed, found, byhead = [], {}, [], [], {}, {}
    started = time.monotonic()

    def add(t, proof):
        if t is None or size(t) > args.maxsize or depth(t) > args.depth or t in known:
            return
        head = t[0] if isinstance(t, tuple) else type(t)
        if any(size(old) <= size(t) and subsumes(old, t) for old in byhead.get(head, ())):
            return
        i = len(nodes)
        known[t] = i
        byhead.setdefault(head, []).append(t)
        nodes.append((t, proof))
        heapq.heappush(pending, (size(t), i))
        for name, target in targets.items():
            if name not in found and subsumes(t, target):
                found[name] = i
                print('FOUND', name, i, word(t), flush=True)

    for axiom in axioms:
        add(canonical(axiom), 'axiom')
    while pending and len(processed) < args.steps and time.monotonic() - started < args.seconds:
        _, i = heapq.heappop(pending)
        x = nodes[i][0]
        if not args.no_modal:
            add(Q(x), ['GEN', i])
        for j in processed + [i]:
            y = nodes[j][0]
            add(detach(x, y), [i, j])
            if i != j:
                add(detach(y, x), [j, i])
        processed.append(i)
        if len(processed) % 100 == 0:
            print('PROGRESS', len(processed), len(nodes), round(time.monotonic() - started, 2), flush=True)
        if {'K', 'P', 'H'} <= found.keys() or 'L' in found:
            break
    for t, proof in nodes:
        if proof == 'axiom':
            continue
        assert (Q(nodes[proof[1]][0]) if proof[0] == 'GEN'
                else detach(nodes[proof[0]][0], nodes[proof[1]][0])) == t
    result = dict(bounds=vars(args), seconds=time.monotonic() - started,
                  processed=len(processed), nodes=len(nodes), found=found,
                  saturated_within_bounds=not pending,
                  derivations=[dict(formula=word(t), term=t, proof=p) for t, p in nodes])
    suffix = 'prop' if args.no_modal else 'modal'
    destination = Path(__file__).parent / f'native_zero_{args.basis}_{args.extra}_{suffix}.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print('DONE', {k: v for k, v in result.items() if k != 'derivations'}, flush=True)


if __name__ == '__main__':
    main()
