#!/usr/bin/env python3
"""Reference kernel for the proposed HA-strength native scalar calculus.

This is a readable reference implementation, not a small Turing machine or
a verified patch of any compressed upstream Python checker.  The 'ipra'
control uses equation-and-zero dispatch; 'ha' uses zero-only dispatch.
Terms: ['z'], ['v', n], ['s', t], ['i', n, a, u, h].
Formulas: ['e', s, t], ['q', y, B], ['d', x, y, B].
Proof constructors are described in ha_transfer.md. Identifiers are naturals.
"""
import json
import sys


class Reject(Exception):
    pass


Z = ['z']


def require(test, message):
    if not test:
        raise Reject(message)


def identifier(n):
    require(type(n) is int and n >= 0, 'Invalid identifier')


def term(t):
    require(type(t) is list and t, 'Invalid term')
    if t == Z:
        return
    if len(t) == 2 and t[0] == 'v':
        identifier(t[1])
        return
    if len(t) == 2 and t[0] == 's':
        term(t[1])
        return
    if len(t) == 5 and t[0] == 'i':
        term(t[1]); term(t[2]); identifier(t[3]); term(t[4])
        return
    raise Reject('Invalid term constructor')


def formula(f):
    require(type(f) is list and f, 'Invalid formula')
    if len(f) == 3 and f[0] == 'e':
        term(f[1]); term(f[2])
        return
    if len(f) == 3 and f[0] == 'q':
        identifier(f[1]); formula(f[2])
        return
    if len(f) == 4 and f[0] == 'd':
        identifier(f[1]); identifier(f[2])
        require(f[1] != f[2], 'D binder names must differ')
        formula(f[3])
        return
    raise Reject('Invalid formula constructor')


def names(a, free=True):
    tag = a[0]
    if tag == 'z':
        return set()
    if tag == 'v':
        return {a[1]}
    if tag == 's':
        return names(a[1], free)
    if tag == 'e':
        return names(a[1], free) | names(a[2], free)
    if tag == 'i':
        body = names(a[4], free)
        body = body - {a[3]} if free else body | {a[3]}
        return names(a[1], free) | names(a[2], free) | body
    binders, body = (a[1:2], a[2]) if tag == 'q' else (a[1:3], a[3])
    result = names(body, free)
    return result - set(binders) if free else result | set(binders)


def fresh(used):
    return 1 + max(used, default=-1)


def substitute(a, sigma):
    """Simultaneous, capture-avoiding substitution of numerical terms."""
    tag = a[0]
    if tag == 'z':
        return a
    if tag == 'v':
        return sigma.get(a[1], a)
    if tag == 's':
        return ['s', substitute(a[1], sigma)]
    if tag == 'e':
        return ['e', substitute(a[1], sigma), substitute(a[2], sigma)]
    if tag == 'i':
        binders, body = [a[3]], a[4]
    elif tag == 'q':
        binders, body = [a[1]], a[2]
    else:
        binders, body = a[1:3], a[3]
    inner = {k: v for k, v in sigma.items() if k not in binders}
    image_names = set().union(*(names(v) for v in inner.values()))
    used = names(a, False) | set(inner) | image_names
    used |= set().union(*(names(v, False) for v in inner.values()))
    new_binders = []
    for binder in binders:
        if binder in image_names:
            new = fresh(used)
            used.add(new)
            body = substitute(body, {binder: ['v', new]})
            new_binders.append(new)
        else:
            new_binders.append(binder)
    body = substitute(body, inner)
    if tag == 'i':
        return ['i', substitute(a[1], sigma), substitute(a[2], sigma), new_binders[0], body]
    if tag == 'q':
        return ['q', new_binders[0], body]
    return ['d', *new_binders, body]


def alpha_key(a, env=()):
    tag = a[0]
    if tag == 'z':
        return ('z',)
    if tag == 'v':
        if a[1] in env:
            return ('bound', env.index(a[1]))
        return ('free', a[1])
    if tag == 's':
        return ('s', alpha_key(a[1], env))
    if tag == 'e':
        return ('e', alpha_key(a[1], env), alpha_key(a[2], env))
    if tag == 'i':
        return ('i', alpha_key(a[1], env), alpha_key(a[2], env), alpha_key(a[4], (a[3],) + env))
    if tag == 'q':
        return ('q', alpha_key(a[2], (a[1],) + env))
    return ('d', alpha_key(a[3], (a[2], a[1]) + env))


def same(a, b):
    return alpha_key(a) == alpha_key(b)


def progress_mode(matrix, witness, logic):
    # This is the exact rule-level change. No computation dispatch is fused
    # with it, so other proof rules are unchanged.
    return witness == Z and (logic == 'ha' or matrix[0] == 'e')


def infer(p, context, logic='ha'):
    require(type(p) is list and p, 'Invalid proof')
    op, *args = p
    if op == 'hyp' and len(args) == 1:
        index = args[0]
        require(type(index) is int and 0 <= index < len(context), 'Invalid hypothesis')
        return context[index]
    if op == 'zero' and len(args) == 3:
        a, u, h = args
        term(a); identifier(u); term(h)
        return ['e', ['i', Z, a, u, h], a]
    if op == 'succ' and len(args) == 4:
        n, a, u, h = args
        term(n); term(a); identifier(u); term(h)
        rec = ['i', n, a, u, h]
        return ['e', ['i', ['s', n], a, u, h], substitute(h, {u: rec})]
    if op == 'tr' and len(args) == 4:
        major, minor, x, body = args
        identifier(x); formula(body)
        equation = infer(major, context, logic)
        require(equation[0] == 'e', 'Transport needs equality')
        left, right = equation[1:]
        require(same(infer(minor, context, logic), substitute(body, {x: left})), 'Transport minor mismatch')
        return substitute(body, {x: right})
    if op == 'qe' and len(args) == 3:
        major, minor, t = args
        term(t)
        closure = infer(major, context, logic)
        require(closure[0] == 'q', 'QE needs Q')
        y, body = closure[1:]
        require(same(infer(minor, context, logic), substitute(body, {y: Z})), 'QE base mismatch')
        return substitute(body, {y: t})
    if op == 'de' and len(args) == 3:
        major, b, minor = args
        identifier(b)
        diagonal = infer(major, context, logic)
        require(diagonal[0] == 'd', 'DE needs D')
        x, y, body = diagonal[1:]
        outer = set().union(*(names(f) for f in context)) | names(diagonal)
        require(b not in outer, 'DE eigenvariable is not fresh')
        opened = substitute(['q', y, body], {x: ['v', b]})
        result = infer(minor, context + [opened], logic)
        require(b not in names(result), 'DE eigenvariable escapes')
        return result
    if op == 'di' and len(args) == 6:
        x, y, body, t, z, minor = args
        identifier(x); identifier(y); identifier(z)
        require(x != y, 'D binder names must differ')
        formula(body); term(t)
        outer = set().union(*(names(f) for f in context)) | (names(body) - {x, y}) | names(t)
        require(z not in outer | {x, y}, 'DI eigenvariable is not fresh')
        eta = ['v', z] if progress_mode(body, t, logic) else Z
        assumption = substitute(body, {x: t, y: eta})
        expected = substitute(body, {x: t, y: ['s', ['v', z]]})
        require(same(infer(minor, context + [assumption], logic), expected), 'DI step mismatch')
        return ['d', x, y, body]
    raise Reject('Unknown proof constructor or arity')


def verify(packet):
    require(type(packet) is dict, 'Expected JSON object')
    logic = packet.get('logic', 'ha')
    require(logic in ('ha', 'ipra'), 'Unknown logic')
    context = packet.get('context', [])
    require(type(context) is list, 'Invalid context')
    for f in context:
        formula(f)
    formula(packet['goal'])
    result = infer(packet['proof'], context, logic)
    require(same(result, packet['goal']), 'Goal mismatch')
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except (Reject, KeyError, ValueError, TypeError, IndexError, RecursionError) as exc:
        print('REJECT:', str(exc), file=sys.stderr)
        sys.exit(1)
    print('ACCEPT')
