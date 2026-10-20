#!/usr/bin/env python3
"""Proof-producing, bounded condensed-detachment search.

Exploratory only. Constants are syntactically fixed; variables are schematic.
Every stored derivation is checked independently by replaying detachment.
"""
import argparse
import heapq
import itertools
import json
from functools import lru_cache
from pathlib import Path
import time


def C(x, y):
    return x, y


@lru_cache(None)
def size(t):
    return 1 if not isinstance(t, tuple) else 1 + size(t[0]) + size(t[1])


def canonical(t):
    vs = {}
    def go(n):
        if isinstance(n, tuple):
            return go(n[0]), go(n[1])
        return vs.setdefault(n, len(vs)) if isinstance(n, int) else n
    return go(t)


def rename(t, offset):
    if isinstance(t, tuple):
        return rename(t[0], offset), rename(t[1], offset)
    return t + offset if isinstance(t, int) else t


@lru_cache(None)
def nvars(t):
    if isinstance(t, tuple):
        return max(nvars(t[0]), nvars(t[1]))
    return t + 1 if isinstance(t, int) else 0


def detach(major, minor):
    if not isinstance(major, tuple):
        return None
    minor = rename(minor, nvars(major))
    bindings = {}
    def deref(t):
        while isinstance(t, int) and t in bindings:
            t = bindings[t]
        return t
    def occurs(v, t):
        t = deref(t)
        return v == t if not isinstance(t, tuple) else occurs(v, t[0]) or occurs(v, t[1])
    stack = [(major[0], minor)]
    while stack:
        a, b = stack.pop()
        a, b = deref(a), deref(b)
        if a == b:
            continue
        if isinstance(b, int) and not isinstance(a, int):
            a, b = b, a
        if isinstance(a, int):
            if occurs(a, b):
                return None
            bindings[a] = b
        elif isinstance(a, tuple) and isinstance(b, tuple):
            stack.extend(zip(a, b))
        else:
            return None
    def substitute(t):
        t = deref(t)
        return (substitute(t[0]), substitute(t[1])) if isinstance(t, tuple) else t
    return canonical(substitute(major[1]))


def subsumes(pattern, target):
    bindings = {}
    stack = [(pattern, target)]
    while stack:
        p, t = stack.pop()
        if isinstance(p, int):
            if p in bindings:
                if bindings[p] != t:
                    return False
            else:
                bindings[p] = t
        elif isinstance(p, tuple):
            if not isinstance(t, tuple):
                return False
            stack.extend(zip(p, t))
        elif p != t:
            return False
    return True


def polish(t):
    if isinstance(t, tuple):
        return 'C' + polish(t[0]) + polish(t[1])
    return str(t) + ',' if isinstance(t, int) else t


def search(maxsize, maxsteps, seconds, constant, extra):
    a, b, c = 0, 1, 2
    u = {'a':a,'b':b,'c':c,'aa':C(a,a),'bb':C(b,b),'cc':C(c,c),'ab':C(a,b),'ac':C(a,c),'ba':C(b,a),'bc':C(b,c),'ca':C(c,a),'cb':C(c,b)}.get(constant,constant)
    L = C(C(C(c, u), a), C(C(a, c), C(b, c)))
    axioms = [canonical(L)]
    if extra == 'truth':
        axioms += ['t']
    if extra == 'explosion':
        axioms += [C('f', 0)]
    if extra == 'dne':
        axioms += [C(C(C(0, 'f'), 'f'), 0)]
    targets = {'I': C(0, 0), 'K': C(0, C(1, 0)),
               'B': C(C(0, 1), C(C(1, 2), C(0, 2))),
               'S': C(C(0, C(1, 2)), C(C(0, 1), C(0, 2))),
               'Peirce': C(C(C(0, 1), 0), 0)}
    nodes = []
    known = {}
    pending = []
    processed = []
    found = {}
    start = time.monotonic()

    def add(t, proof):
        if t is None or size(t) > maxsize or t in known:
            return
        # A weaker instance does not help unrestricted substitution/detachment.
        if any(size(u) <= size(t) and subsumes(u, t) for u in known):
            return
        i = len(nodes)
        known[t] = i
        nodes.append((t, proof))
        heapq.heappush(pending, (size(t), i))
        for name, target in targets.items():
            if name not in found and subsumes(t, target):
                found[name] = i
                print('FOUND', name, i, polish(t), flush=True)

    for ax in axioms:
        add(ax, 'axiom')
    while pending and len(processed) < maxsteps and time.monotonic() - start < seconds:
        _, i = heapq.heappop(pending)
        a = nodes[i][0]
        for j in processed + [i]:
            b = nodes[j][0]
            add(detach(a, b), [i, j])
            if i != j:
                add(detach(b, a), [j, i])
        processed.append(i)
        if len(processed) % 100 == 0:
            print('PROGRESS', len(processed), len(nodes), size(a), time.monotonic()-start, flush=True)
        if {'K', 'S'} <= found.keys():
            break
    for t, proof in nodes:
        if proof != 'axiom':
            assert detach(nodes[proof[0]][0], nodes[proof[1]][0]) == t
    result = dict(constant=constant, extra=extra, maxsize=maxsize,
                  seconds=time.monotonic()-start, processed=len(processed),
                  nodes=len(nodes), found=found,
                  derivations=[dict(formula=polish(t), term=t, proof=p) for t,p in nodes])
    print('DONE', {k:v for k,v in result.items() if k != 'derivations'}, flush=True)
    out = Path(__file__).parent / ('restricted_L_' + constant + '_' + extra + '.json')
    out.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--maxsize', type=int, default=31)
    ap.add_argument('--maxsteps', type=int, default=2000)
    ap.add_argument('--seconds', type=float, default=120)
    ap.add_argument('--constant', default='f')
    ap.add_argument('--extra', choices=['none','truth','explosion','dne'], default='none')
    args = ap.parse_args()
    search(args.maxsize, args.maxsteps, args.seconds, args.constant, args.extra)
