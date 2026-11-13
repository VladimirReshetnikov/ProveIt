"""Exhaustive finite syntax search through nine native-iterator nodes.

This independently reproduces the already-known nine-node clock lower bound
in ConciseIPRA ch01_base.tex. It is an archived experiment, not a smaller
axiomatization. All evaluations are exact and have no semantic cutoffs.
"""
from functools import lru_cache
from itertools import product
import json


@lru_cache(None)
def terms(size, variables):
    if size == 1:
        return (('z',),) + tuple(('v', i) for i in range(variables))
    out = [('s', a) for a in terms(size - 1, variables)]
    for a in range(1, size - 2):
        for b in range(1, size - a - 1):
            c = size - 1 - a - b
            if c > 0:
                out += [('i', n, seed, body)
                        for n, seed, body in product(terms(a, variables),
                                                    terms(b, variables),
                                                    terms(c, variables + 1))]
    return tuple(out)


def evaluate(t, env):
    if t[0] == 'z':
        return 0
    if t[0] == 'v':
        return env[t[1]]
    if t[0] == 's':
        return evaluate(t[1], env) + 1
    n = evaluate(t[1], env)
    a = evaluate(t[2], env)
    for _ in range(n):
        a = evaluate(t[3], env + (a,))
    return a


def show(t, names=('v',)):
    if t[0] == 'z':
        return '0'
    if t[0] == 'v':
        return names[t[1]]
    if t[0] == 's':
        return 'S(' + show(t[1], names) + ')'
    name = 'u' + str(len(names))
    return ('I(' + show(t[1], names) + ', ' + show(t[2], names)
            + '; ' + name + '.' + show(t[3], names + (name,)) + ')')


def main():
    for size in range(1, 10):
        hits = []
        max_first = max_second = 0
        for t in terms(size, 1):
            a = evaluate(t, (0,))
            max_first = max(max_first, a)
            if a == 0:
                continue
            b = evaluate(t, (a,))
            max_second = max(max_second, b)
            if b in (0, a):
                continue
            if evaluate(t, (b,)) == 0:
                hits.append({'term': show(t), 'a': a, 'b': b})
        print(json.dumps({'size': size, 'count': len(terms(size, 1)),
                          'max_f0': max_first, 'max_ff0': max_second,
                          'hits': hits}), flush=True)


if __name__ == '__main__':
    main()
