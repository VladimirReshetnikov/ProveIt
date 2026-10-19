#!/usr/bin/env python3
"""A complete ground-equational refutation-search specification, not a TM.

Search is fair by enumeration of all finite binary certificates. Acceptance
requires literal, contextual, ground instances of the supplied equations.
Timeout, malformed input and finite-search exhaustion never mean refutation.
This module uses only Python's standard library. No consistency oracle is used.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path

def freeze(t):
    return t if isinstance(t, str) else tuple(freeze(x) for x in t)

def variables(t):
    todo, names = [t], set()
    while todo:
        x = todo.pop()
        if isinstance(x, str):
            names.add(x)
        else:
            todo.extend(x[1:])
    return names

def subst(t, assignment):
    todo, values = [(t, False)], []
    while todo:
        x, finish = todo.pop()
        if isinstance(x, str):
            values.append(assignment[x])
        elif finish:
            arity = len(x) - 1
            children = values[-arity:] if arity else []
            if arity:
                del values[-arity:]
            values.append((x[0], *children))
        else:
            todo.append((x, True))
            todo.extend((y, False) for y in reversed(x[1:]))
    assert len(values) == 1
    return values[0]

def equal(a, b):
    todo = [(a, b)]
    while todo:
        x, y = todo.pop()
        if isinstance(x, str) or isinstance(y, str):
            if x != y:
                return False
        elif len(x) != len(y) or x[0] != y[0]:
            return False
        else:
            todo.extend(zip(x[1:], y[1:]))
    return True

def replace(t, path, expected, replacement):
    zipper = []
    for i in path:
        if isinstance(t, str) or not 0 <= i < len(t) - 1:
            raise ValueError('invalid context path')
        zipper.append((t, i))
        t = t[i + 1]
    if not equal(t, expected):
        raise ValueError('left instance does not match the selected subterm')
    t = replacement
    for parent, i in reversed(zipper):
        children = list(parent[1:])
        children[i] = t
        t = (parent[0], *children)
    return t

class Reader:
    def __init__(self, bits, signature):
        if set(bits) - {'0', '1'}:
            raise ValueError('nonbinary certificate')
        self.bits, self.pos = bits, 0
        self.signature = signature
        self.symbols = list(signature)
        self.width = max(1, (len(signature) - 1).bit_length())

    def take(self, n):
        end = self.pos + n
        if end > len(self.bits):
            raise ValueError('truncated field')
        s = self.bits[self.pos:end]
        self.pos = end
        return int(s, 2) if s else 0

    def natural(self):
        zeros = 0
        while self.take(1) == 0:
            zeros += 1
        return (1 << zeros) + self.take(zeros) - 1

    def term(self):
        # Explicit arity stack: no input-dependent parser recursion.
        stack = []
        while True:
            tag = self.take(self.width)
            if tag >= len(self.symbols):
                raise ValueError('unused symbol code')
            name = self.symbols[tag]
            arity = self.signature[name]
            if arity:
                stack.append([name, arity, []])
                continue
            value = (name,)
            while stack:
                name, remaining, args = stack[-1]
                args.append(value)
                stack[-1][1] -= 1
                if remaining > 1:
                    break
                stack.pop()
                value = (name, *args)
            else:
                return value

def validate(bits, signature, equations, start, target):
    """Return (accepted, trace length); reject invalid certificates explicitly.

    All equation variables, including variables appearing only on one side,
    receive one ground term each; repeated occurrences reuse that exact term.
    """
    reader = Reader(bits, signature)
    steps = reader.natural()
    current = start
    for _ in range(steps):
        rule, reverse = reader.natural(), reader.take(1)
        if rule >= len(equations):
            raise ValueError('unknown equation')
        path = [reader.natural() for _ in range(reader.natural())]
        eq = equations[rule]
        names = sorted(variables(eq[0]) | variables(eq[1]))
        assignment = {name: reader.term() for name in names}
        a, b = subst(eq[reverse], assignment), subst(eq[1 - reverse], assignment)
        current = replace(current, path, a, b)
    if reader.pos != len(bits):
        raise ValueError('trailing bits')
    return equal(current, target), steps

def nat(n):
    if type(n) is not int or n < 0:
        raise ValueError('natural required')
    s = bin(n + 1)[2:]
    return '0' * (len(s) - 1) + s

def encode_term(t, signature):
    symbols = list(signature)
    width = max(1, (len(signature) - 1).bit_length())
    todo, out = [t], []
    while todo:
        x = todo.pop()
        if isinstance(x, str) or x[0] not in signature or len(x) != signature[x[0]] + 1:
            raise ValueError('malformed or nonground term')
        out.append(format(symbols.index(x[0]), f'0{width}b'))
        todo.extend(reversed(x[1:]))
    return ''.join(out)

def encode(steps, signature, equations):
    out = [nat(len(steps))]
    for rule, reverse, path, assignment in steps:
        if reverse not in (0, 1):
            raise ValueError('orientation must be zero or one')
        out += [nat(rule), str(reverse), nat(len(path))]
        out += [nat(i) for i in path]
        a, b = equations[rule]
        names = sorted(variables(a) | variables(b))
        if set(names) != set(assignment):
            raise ValueError('missing or extraneous equation-variable substitution')
        out += [encode_term(assignment[name], signature) for name in names]
    return ''.join(out)

def search(signature, equations, start, target, max_code=None):
    # Binary(n) without its leading one enumerates every finite binary word.
    # A finite bound is an experiment, not the unbounded semidecision procedure.
    for code in itertools.count(1):
        if max_code is not None and code > max_code:
            return {'status': 'FINITE_BOUND_EXHAUSTED', 'last_code': max_code}
        bits = bin(code)[3:]
        try:
            yes, length = validate(bits, signature, equations, start, target)
        except ValueError:
            continue
        # Resource/recursion exceptions are deliberately not converted to YES.
        if yes:
            return {'status': 'CERTIFIED_GROUND_DERIVATION', 'code': code,
                    'steps': length, 'certificate_bits': bits}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('packet', type=Path)
    p.add_argument('--max-code', type=int, default=65536,
                   help='finite experiment bound; does not establish nonderivability')
    p.add_argument('--unbounded', action='store_true', help='fair but extremely inefficient search')
    a = p.parse_args()
    data = json.loads(a.packet.read_text())
    result = search(data['signature'], [tuple(map(freeze, e)) for e in data['equations']],
                    freeze(data['start']), freeze(data['target']),
                    None if a.unbounded else a.max_code)
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
