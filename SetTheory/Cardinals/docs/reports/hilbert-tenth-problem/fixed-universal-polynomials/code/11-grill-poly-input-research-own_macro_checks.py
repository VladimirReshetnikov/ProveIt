# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent, small mathematical tests. Executes no downloaded source."""
from collections import deque
import json

def sym(name, i=0):
    return (name, i)

def canonical(i, M, N):
    A, a, B, b, x = [sym(k, i) for k in ('A', 'a', 'B', 'b', 'x')]
    return [A, x] + [a, x] * M + [B, x] + [b, x] * N

def rules(direction, write, corrected=True):
    d = {}

    def add(a, *bs):
        d[sym(a)] = list(bs)
    x = sym('x')
    C = sym('C')
    c = sym('c')
    if direction == 'R':
        add('A', C, x, *[c, x] * write)
        add('a', c, x, c, x)
        add('B', sym('S'))
        add('b', sym('s'))
    else:
        add('A', sym('L'), x)
        add('a', sym('l'), x)
        add('B', C, x, *[c, x] * write)
        add('b', c, x, c, x)
        add('L', sym('S'))
        add('l', sym('s'))
    for a, b, c_ in [('C', 'D1', 'D0'), ('c', 'd1', 'd0'), ('S', 'T1', 'T0'), ('s', 't1', 't0')]:
        add(a, sym(b), sym(c_))
    for r in (0, 1):
        j = r + 1
        xx = sym('x', j)
        head, low = ('A', 'a') if direction == 'R' else ('Bp', 'bp')
        prod = [sym(head, j), xx]
        if r == 0:
            prod = [xx] + prod
        add('D' + str(r), *prod)
        add('d' + str(r), sym(low, j), xx)
        head, low = ('B', 'b') if direction == 'R' else ('A', 'a')
        add('T' + str(r), sym(head, j), xx)
        add('t' + str(r), sym(low, j), *([xx] if corrected or r else []))
        if direction == 'L':
            d[sym('Bp', j)] = [sym('B', j), xx]
            d[sym('bp', j)] = [sym('b', j), xx]
        d[sym('A', j)] = [sym('H')]
        for a in ('a', 'B', 'b', 'x'):
            d[sym(a, j)] = [sym('Z'), sym('Z')]
    d[sym('Z')] = [sym('Z'), sym('Z')]
    return d

def one_macro(direction, write, M, N, corrected=True):
    r = (N if direction == 'R' else M) % 2
    j = r + 1
    target = canonical(j, 2 * M + write, N // 2) if direction == 'R' else canonical(j, M // 2, 2 * N + write)
    q = deque(canonical(0, M, N))
    d = rules(direction, write, corrected)
    minimum = len(q)
    steps = 0
    while list(q) != target:
        if not len(q) >= 2:
            raise RuntimeError(('premature short queue', direction, write, M, N, list(q)))
        a = q.popleft()
        q.popleft()
        if not a[0] != 'x':
            raise RuntimeError(('filler unexpectedly read', a))
        if not (a[1] == 0 or a[0] in ('Bp', 'bp')):
            raise RuntimeError(('target head read before boundary', a, list(q)))
        q.extend(d[a])
        steps += 1
        minimum = min(minimum, len(q))
        if not steps < 10000:
            raise RuntimeError('Invariant failed at original source line 51')
    return (steps, minimum)

def genera_head(direction, write, M, N):
    q = canonical(0, M, N)
    d = rules(direction, write)
    p = 0
    gens = 0
    reads = 0
    while not any((x[0] == 'H' for x in q)):
        out = []
        for a in q:
            if p == 0:
                if not a[0] != 'x':
                    raise RuntimeError('Invariant failed at original source line 60')
                if a[0] == 'A' and a[1] != 0:
                    reads += 1
                out.extend(d[a])
            p ^= 1
        q = out
        gens += 1
        if not (q and gens < 100):
            raise RuntimeError('Invariant failed at original source line 65')
    if not (sum((x[0] == 'H' for x in q)) == 1 and reads == 1):
        raise RuntimeError('Invariant failed at original source line 66')
    return gens

def old_discrepancy():
    q = deque(canonical(0, 0, 2))
    d = rules('R', 0, False)
    for _ in range(10):
        a = q.popleft()
        q.popleft()
        q.extend(d[a])
    return list(q)

def exponent_checks():
    count = 0
    for k in range(4, 9):
        for n in range(2, 15):
            q = 2 ** n
            B = 2 ** (k - 1) * q ** k
            J = (B ** n - 1) // (B - 1)
            if not 2 <= n < B - 1:
                raise RuntimeError('Invariant failed at original source line 81')
            v = (J - n) // (B - 1)
            g = B - 1 - n
            if not (v > 0 and g > 0 and ((B - 1) * v + n == J) and (n + g == B - 1)):
                raise RuntimeError('Invariant failed at original source line 83')
            for wrong in (n + B - 1, n - (B - 1), 1, B - 1):
                if not not (1 <= wrong <= B - 2 and (J - wrong) % (B - 1) == 0):
                    raise RuntimeError('Invariant failed at original source line 85')
            count += 1
    return count
if __name__ == '__main__':
    counts = {'macro_cases': 0, 'genera_unique_H_cases': 0, 'tag_steps': 0}
    minimum = 10 ** 9
    maxgens = 0
    for direction in ('R', 'L'):
        for write in (0, 1):
            for M in range(33):
                for N in range(33):
                    t, m = one_macro(direction, write, M, N)
                    counts['macro_cases'] += 1
                    counts['tag_steps'] += t
                    minimum = min(minimum, m)
                    if M <= 16 and N <= 16:
                        maxgens = max(maxgens, genera_head(direction, write, M, N))
                        counts['genera_unique_H_cases'] += 1
    counts.update(minimum_preaccept_word_length=minimum, max_generations_to_H=maxgens, exponent_outer_cases=exponent_checks(), printed_t0_after_ten_steps=old_discrepancy())
    print(json.dumps(counts, indent=2))
