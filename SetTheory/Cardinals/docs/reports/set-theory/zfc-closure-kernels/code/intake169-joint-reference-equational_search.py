#!/usr/bin/env python3
"""Exact ground-rewrite certificates and fair natural-number enumeration.

The checker proves equations of the supplied equational theory.  It does not
decide truth of the input clauses, and is not a Turing-machine state compiler.
Only Python's standard library is required.
"""
from __future__ import annotations

from functools import lru_cache
from math import isqrt
import argparse
import json
from pathlib import Path


def freeze(value):
    return tuple(freeze(x) for x in value) if isinstance(value, (tuple, list)) else value


def variables(term):
    if isinstance(term, str):
        return {term}
    return set().union(*(variables(x) for x in term[1:]))


def nodes(term):
    return 1 if isinstance(term, str) else 1 + sum(nodes(x) for x in term[1:])


def natural(n):
    return type(n) is int and n >= 0


def validate_term(term, signature, ground=False):
    if isinstance(term, str):
        if ground or not term:
            raise ValueError('variable in a ground term or empty variable name')
        return
    if not isinstance(term, tuple) or not term or term[0] not in signature:
        raise ValueError('unknown or malformed constructor')
    if len(term) != signature[term[0]] + 1:
        raise ValueError('wrong constructor arity')
    for child in term[1:]:
        validate_term(child, signature, ground)


def substitute(term, environment):
    if isinstance(term, str):
        return environment[term]
    return (term[0],) + tuple(substitute(x, environment) for x in term[1:])


def replace(term, address, old, new):
    if not address:
        if term != old:
            raise ValueError('instantiated left side does not match the selected subtree')
        return new
    index = address[0]
    if not natural(index) or index >= len(term) - 1:
        raise ValueError('invalid child address')
    children = list(term[1:])
    children[index] = replace(children[index], address[1:], old, new)
    return (term[0],) + tuple(children)


class Kernel:
    def __init__(self, signature, equations, start, target):
        self.signature = dict(signature)
        if not self.signature or any(not natural(n) for n in self.signature.values()):
            raise ValueError('invalid signature')
        self.constants = [s for s, n in self.signature.items() if n == 0]
        self.functions = [s for s, n in self.signature.items() if n]
        if not self.constants or not self.functions:
            raise ValueError('the numeric codec requires a constant and a proper function')
        self.equations = freeze(equations)
        if not self.equations:
            raise ValueError('empty equation list')
        for eq in self.equations:
            if len(eq) != 2:
                raise ValueError('malformed equation')
            for term in eq:
                validate_term(term, self.signature)
        self.rule_variables = [sorted(variables(a) | variables(b)) for a, b in self.equations]
        self.start, self.target = freeze(start), freeze(target)
        validate_term(self.start, self.signature, True)
        validate_term(self.target, self.signature, True)

    def step(self, current, step):
        if not isinstance(step, dict) or set(step) != {'rule', 'reverse', 'address', 'values'}:
            raise ValueError('malformed step fields')
        rule, reverse = step['rule'], step['reverse']
        if not natural(rule) or rule >= len(self.equations) or type(reverse) is not bool:
            raise ValueError('invalid rule or orientation')
        address, values = step['address'], step['values']
        if not isinstance(address, (list, tuple)) or not all(natural(n) for n in address):
            raise ValueError('malformed address')
        if not isinstance(values, (list, tuple)) or len(values) != len(self.rule_variables[rule]):
            raise ValueError('wrong substitution length')
        values = freeze(values)
        for value in values:
            validate_term(value, self.signature, True)
        environment = dict(zip(self.rule_variables[rule], values))
        left, right = self.equations[rule]
        if reverse:
            left, right = right, left
        return replace(current, address, substitute(left, environment), substitute(right, environment))

    def check(self, proof, trace=False):
        current = self.start
        history = [current]
        try:
            if not isinstance(proof, (list, tuple)):
                return (False, history) if trace else False
            for step in proof:
                current = self.step(current, step)
                history.append(current)
            answer = current == self.target
        except (KeyError, TypeError, ValueError, IndexError):
            answer = False
        return (answer, history) if trace else answer

    @lru_cache(maxsize=None)
    def decode_term(self, n):
        if not natural(n):
            raise ValueError('invalid natural-number term code')
        if n < len(self.constants):
            return (self.constants[n],)
        payload, index = divmod(n - len(self.constants), len(self.functions))
        symbol = self.functions[index]
        args = unpack_tuple(payload, self.signature[symbol])
        # Every child code is at most payload and strictly smaller than n.
        return (symbol,) + tuple(self.decode_term(x) for x in args)

    def encode_term(self, term):
        term = freeze(term)
        validate_term(term, self.signature, True)
        if not self.signature[term[0]]:
            return self.constants.index(term[0])
        return (len(self.constants) + self.functions.index(term[0]) + len(self.functions)
                * pack_tuple([self.encode_term(x) for x in term[1:]]))

    def decode_step(self, n):
        if not natural(n):
            raise ValueError('invalid step code')
        payload, orientation = divmod(n, 2 * len(self.equations))
        address, values = unpair(payload)
        return {'rule': orientation // 2, 'reverse': bool(orientation % 2),
                'address': unpack_list(address),
                'values': [self.decode_term(v) for v in unpack_list(values)]}

    def encode_step(self, step):
        orientation = 2 * step['rule'] + int(step['reverse'])
        address = pack_list(step['address'])
        values = pack_list([self.encode_term(v) for v in step['values']])
        return orientation + 2 * len(self.equations) * pair(address, values)

    def decode_proof(self, n):
        return [self.decode_step(k) for k in unpack_list(n)]

    def encode_proof(self, proof):
        return pack_list([self.encode_step(s) for s in proof])

    def search(self, stop=None):
        """Ideal complete enumerator; stop supplies a finite demonstration bound."""
        n = 0
        while stop is None or n < stop:
            if self.check(self.decode_proof(n)):
                return n
            n += 1
        return None


def pair(a, b):
    if not natural(a) or not natural(b):
        raise ValueError('pairing requires natural numbers')
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    if not natural(n):
        raise ValueError('unpairing requires a natural number')
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    b = n - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def pack_tuple(items):
    if len(items) == 1:
        return items[0]
    return pair(items[0], pack_tuple(items[1:]))


def unpack_tuple(n, arity):
    if arity == 1:
        return [n]
    a, rest = unpair(n)
    return [a] + unpack_tuple(rest, arity - 1)


def pack_list(items):
    result = 0
    for item in reversed(items):
        result = 1 + pair(item, result)
    return result


def unpack_list(n):
    if not natural(n):
        raise ValueError('list code is not a natural number')
    items = []
    while n:
        item, n = unpair(n - 1)
        items.append(item)
    return items


def from_file(path):
    data = json.loads(Path(path).read_text())
    return Kernel(data['signature'], data['equations'], data['start'], data['target'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('theory', type=Path)
    parser.add_argument('--proof', type=Path)
    parser.add_argument('--code', type=int)
    parser.add_argument('--search-below', type=int)
    args = parser.parse_args()
    kernel = from_file(args.theory)
    if args.proof:
        proof = json.loads(args.proof.read_text())
        print(json.dumps({'accepted': kernel.check(proof), 'code': kernel.encode_proof(proof)}))
    elif args.code is not None:
        print(json.dumps({'accepted': kernel.check(kernel.decode_proof(args.code))}))
    else:
        print(json.dumps({'found': kernel.search(args.search_below)}))


if __name__ == '__main__':
    main()
