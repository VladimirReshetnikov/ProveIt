"""Untrusted compiler to one-term crossed backward substitution.

An equation-only Back step with goal a=d is replaced by two Cross steps:
  b=t, a[t/b]=d[t/b]  ->  d[t/b]=a
  b=t, d[t/b]=a      ->  a=d.
The major proof is repeated in the same world, not moved to another scope.
"""
import json
import sys
import crossed_back as X
import equation_back as E
from compile_equational import diagonal, translate as to_equations


def convert(proof, context=(), scope=0):
    context = list(context)
    tag, *args = proof
    if tag == 'c':
        return proof
    if tag == 'u':
        index, premise = args
        return [tag, index, convert(premise, context, scope) if context[index][0] else None]
    if tag == 'v':
        (a, d), major, minor = args
        p = convert(major, context, scope)
        return ['v', d, p, ['v', a, p, convert(minor, context, scope)]]
    if tag == 'a':
        term, branch = args
        extended = context + [([], [-scope - 1, term])]
        return [tag, term, convert(branch, extended, scope + 1)]
    if tag == 'e':
        goal, major, branch = args
        paired = E.derive(major, context, scope)
        body = E.opening(paired[0], -scope - 1, 2)
        extended = context + [(E.opening(body, 0), body)]
        return [tag, goal, convert(major, context, scope), convert(branch, extended, scope + 1)]
    if tag == 'i':
        goal, branch = args
        body = E.opening(goal[0], -scope, 2)
        eta = -scope - 1 if diagonal(goal[0]) else 0
        extended = context + [([], E.opening(body, eta))]
        return [tag, goal, convert(branch, extended, scope + 1)]
    raise ValueError('unknown rule')


def translate(data):
    intermediate = to_equations(data)
    result = {'goal': intermediate['goal'], 'proof': convert(intermediate['proof'])}
    X.verify(result)
    return result


if __name__ == '__main__':
    json.dump(translate(json.load(sys.stdin)), sys.stdout, separators=(',', ':'))
    print()
