#!/usr/bin/env python3
"""Independent finite-component, radius-local, and orbit checks.
Only standard library; exact integer arithmetic throughout.
"""
from itertools import combinations, product
from random import Random
PATS = {'E': (frozenset({(0, 0), (1, 0)}), frozenset({(1, 0), (2, 0)})), 'W': (frozenset({(0, 0), (2, 0)}), frozenset({(-1, 0), (1, 0)})), 'R': (frozenset({(0, 0), (1, 0), (3, 0)}), frozenset({(-1, 0), (1, 0), (4, 1)})), 'L': (frozenset({(0, 0), (2, 0), (4, 0)}), frozenset({(0, 1), (3, 1), (4, 1)}))}
NEAR = [(i, j) for i in range(-2, 3) for j in range(-2, 3) if (i, j) != (0, 0)]

def add(a, b):
    return (a[0] + b[0], a[1] + b[1])

def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])

def trans(P, a):
    return {add(p, a) for p in P}

def norm(a):
    return max(map(abs, a))

def neighborhood(P):
    return {add(p, (i, j)) for p in P for i in range(-2, 3) for j in range(-2, 3)}

def components(S):
    todo = set(S)
    while todo:
        p = todo.pop()
        c = {p}
        stack = [p]
        while stack:
            q = stack.pop()
            for d in NEAR:
                r = add(q, d)
                if r in todo:
                    todo.remove(r)
                    c.add(r)
                    stack.append(r)
        yield c

def recognized(C):
    matches = []
    for name, (P, Q) in PATS.items():
        p = next(iter(P))
        for q in C:
            a = sub(q, p)
            if trans(P, a) == C:
                matches.append((name, a))
    if not len(matches) <= 1:
        raise RuntimeError(('ambiguous', C, matches))
    return matches[0] if matches else None

def component_step(S):
    out = set()
    for C in components(S):
        match = recognized(C)
        O = trans(PATS[match[0]][1], match[1]) if match else C
        if not not out & O:
            raise RuntimeError(('collision', S, out & O))
        out |= O
    if not len(out) == len(S):
        raise RuntimeError(('mass', S, out))
    return out

def local_bit(S, z):

    def active(name, a):
        P, Q = PATS[name]
        PP = trans(P, a)
        NN = neighborhood(PP)
        if not all((norm(sub(u, z)) <= 6 for u in NN)):
            raise RuntimeError('Audit check failed: all((norm(sub(u, z)) <= 6 for u in NN))')
        return PP <= S and (not NN - PP & S)
    old_removed = False
    new_added = False
    for name, (P, Q) in PATS.items():
        for r in P | Q:
            a = sub(z, r)
            if active(name, a):
                if r in P:
                    old_removed = True
                if r in Q:
                    new_added = True
    return int(new_added or (z in S and (not old_removed)))

def section(k, n):
    return {(0, n), (3, n), (4, n), (k + n, n)}

def stage(k, n, j, phase):
    K = k + n
    if phase == 'E':
        return {(0, n), (3 + j, n), (4 + j, n), (K, n)}
    return {(0, n), (K - 4 - j, n), (K - 2 - j, n), (K + 1, n + 1)}

def T(k, n):
    return n * n + (2 * k - 11) * n

def formula_visited(k, n):
    return {(0, n), (k + n, n)} | {(x, n) for x in range(2, k + n - 1)}

def formula_count(k, N):
    if N == 0:
        return 1
    if N <= k - 2:
        return N * (N + 1)
    return (N * N + (2 * k - 1) * N - k * k + 3 * k - 4) // 2

def main():
    checks = 0
    domain = list(product(range(-1, 6), range(2)))
    for size in range(5):
        for occupied in combinations(domain, size):
            S = set(occupied)
            out = component_step(S)
            candidates = {add(p, d) for p in S for d in product(range(-1, 2), repeat=2)}
            if not {z for z in candidates if local_bit(S, z)} == out:
                raise RuntimeError('Audit check failed: {z for z in candidates if local_bit(S, z)} == out')
            checks += 1
    rng = Random(20261003)
    for _ in range(250):
        S = {(rng.randrange(-12, 13), rng.randrange(-8, 9)) for _ in range(rng.randrange(50))}
        component_step(S)
        checks += 1
    for name, (P, Q) in PATS.items():
        for dx in range(-7, 8):
            for dy in range(-4, 5):
                S = set(P) | trans({(0, 0), (1, 0), (1, 1), (2, 1)}, (dx, dy))
                component_step(S)
                checks += 1
    orbits = 0
    for k in range(7, 31):
        S = section(k, 0)
        visited = set(S)
        t = 0
        for n in range(25):
            if not (t == T(k, n) and S == section(k, n)):
                raise RuntimeError('Audit check failed: t == T(k, n) and S == section(k, n)')
            for phase in ['E', 'W']:
                for j in range(k + n - 5):
                    if not S == stage(k, n, j, phase):
                        raise RuntimeError((k, n, t, phase, j, S))
                    visited |= S
                    S = component_step(S)
                    t += 1
            if not S == section(k, n + 1):
                raise RuntimeError('Audit check failed: S == section(k, n + 1)')
        visited |= S
        for n in range(25):
            if not {p for p in visited if p[1] == n} == formula_visited(k, n):
                raise RuntimeError('Audit check failed: {p for p in visited if p[1] == n} == formula_visited(k, n)')
        for N in range(25):
            C = sum((-N <= x <= N and -N <= y <= N for x, y in visited))
            if not C == formula_count(k, N):
                raise RuntimeError((k, N, C, formula_count(k, N)))
        orbits += 1
    print(f'PASS: {checks} finite configurations; {orbits} orbits through 25 completed rounds each; exact phase, mass, local-radius, visited-row and centered-box-count assertions.')
    print('Radius bounds:', {name: max((norm(sub(p, r)) for p in P for r in P | Q)) + 2 for name, (P, Q) in PATS.items()})
if __name__ == '__main__':
    main()
