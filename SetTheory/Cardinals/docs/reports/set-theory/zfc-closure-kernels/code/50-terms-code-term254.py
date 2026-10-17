#!/usr/bin/env python3
"""Constructor-only ground-term certificates for the exact twelve C254 rules.

The verifier performs no arithmetic on represented natural numbers: no numeric
literals, pairing, inverse pairing, quotation or formula materialization. Its
indices and rule tags remain ordinary finite integers. Default target is the
fixed falsity term B_1(Z,Z); a caller can explicitly supply another arena ID.

This is an experimental reference checker, not a binary codec, enumerating
Turing machine, Lean proof, PA internalization or new state bound.
"""
from copy import deepcopy

import canonical254 as canonical
from symbolic254 import ARITY


class TermArena(canonical.CanonicalArena):
    """Reuse exact constructors and macros, with no numeric literal table."""
    def __init__(self):
        self.nodes = [('z',)]
        self.index = {('z',): 0}
        self.frozen = False
        self.comparisons = 0

    def literal(self, n):
        # The fixed templates use only 0 and F=1. These are term constants,
        # not a general numeric-to-term decoder.
        if type(n) is int and n == 0:
            return 0
        if type(n) is int and n == 1:
            return self.b(1, 0, 0)
        raise ValueError('A ground-term template requested a numeric literal')


def verify_certificate(cert, goal=None):
    """Check a finite certificate, defaulting to the fixed falsity term.

    `goal` is a trusted caller-supplied arena ID, never read from the certificate.
    For a consistency search call this function with no `goal` argument.
    `goal=0` is useful for controls, but is a different search problem.
    """
    try:
        if type(cert) is not dict or cert.get('format') != 'term-c254-v1':
            return False
        nodes = cert['nodes']
        if type(nodes) is not list or not nodes or nodes[0] != ['z']:
            return False
        arena = TermArena()
        for i, raw in enumerate(nodes[1:], 1):
            if type(raw) is not list or len(raw) != 4 or raw[0] != 'b':
                return False
            _, tag, x, y = raw
            if type(tag) is not int or not 0 <= tag < 4:
                return False
            if not all(type(j) is int and 0 <= j < i for j in (x, y)):
                return False
            if (tag, x, y) == (0, 0, 0) or tuple(raw) in arena.index:
                return False
            arena.index[tuple(raw)] = i
            arena.nodes.append(tuple(raw))
        arena.frozen = True
        if goal is None:
            target = arena.b(1, 0, 0)
        elif type(goal) is int and 0 <= goal < len(nodes):
            target = goal
        else:
            return False
        rows = cert['proof_rows']
        if type(rows) is not list:
            return False
        formulas = []
        for i, row in enumerate(rows):
            if type(row) is not dict:
                return False
            tag, args, children = row['tag'], row['args'], row['children']
            if type(tag) is not int or not 0 <= tag < 12:
                return False
            if type(args) is not list or len(args) != ARITY[tag]:
                return False
            if not all(type(j) is int and 0 <= j < len(nodes) for j in args):
                return False
            if type(children) is not list or len(children) != (
                    2 if tag == 1 else 1 if tag == 2 else 0):
                return False
            if not all(type(j) is int and 0 <= j < i for j in children):
                return False
            if tag == 0:
                out = 0
            elif tag == 1:
                out = args[0]
                if formulas[children[1]] != arena.apply(
                        'wim', [formulas[children[0]], out]):
                    return False
            elif tag == 2:
                out = arena.apply('wal', [args[0], formulas[children[0]]])
            elif tag == 11:
                # Canonical IDs agree iff the denoted naturals agree.
                if args[2] == args[0] or args[2] == args[1]:
                    return False
                out = arena.apply('bundle', args)
            else:
                out = arena.apply('rho' + str(tag - 2), args)
            if type(row['formula']) is not int or row['formula'] != out:
                return False
            formulas.append(out)
        return bool(formulas) and formulas[-1] == target
    except (ValueError, TypeError, KeyError, IndexError, RecursionError):
        return False


def from_canonical(cert):
    """Convert an accepted canonical certificate; return (term_cert, goal_ID).

    This is a producer/adapter, separate from the ground-term verifier. It may
    invoke canonical verification. Numeric argument fields are replaced with
    their certified term roots; all literal and legacy-code records are dropped.
    The returned goal must be passed explicitly for a target other than F.
    """
    if not canonical.verify_certificate(cert):
        raise ValueError('Source canonical certificate was not accepted')
    roots = {row['value']: row['node'] for row in cert['literals']}
    converted = {
        'format': 'term-c254-v1',
        'nodes': deepcopy(cert['nodes']),
        'proof_rows': [
            {'tag': row['tag'], 'args': [roots[v] for v in row['args']],
             'children': list(row['children']), 'formula': row['formula']}
            for row in cert['proof_rows']],
    }
    goal = roots[cert['conclusion']]
    if not verify_certificate(converted, goal=goal):
        raise ValueError('Canonical-to-term conversion did not verify')
    return converted, goal
