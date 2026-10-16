#!/usr/bin/env python3
"""PSC refutations via generic Skolem clauses and a linear ground tableau.

Only qpsc_syntax.py's attributed formula parser/wrapper is reused.  The generic
signed clausifier, linear trail checker, and candidate codec are new reference
implementations.  No binary Turing-machine state count or formal verification
claim is attached to this Python program.  Every operation below is total on
finite mathematical input with unbounded storage; host exhaustion is an error,
never an accepted refutation.  Equality is deliberately absent from the input.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import itertools
import json
from math import isqrt
from pathlib import Path

import qpsc_syntax as syntax

# Source variable i is the integer i. Function application is (symbol, *args).
# Symbol 0 is a permanently available dummy constant for nonempty domains.
# A literal is (positive, left_term, right_term), using the single predicate E.


def nat(n):
    if type(n) is not int or n < 0:
        raise ValueError('Expected a nonnegative integer, not a Boolean')
    return n


def variables(term):
    if type(term) is int:
        return {term}
    return set().union(*(variables(t) for t in term[1:]))


def ground_term(raw, signature):
    if not isinstance(raw, (list, tuple)) or not raw:
        raise ValueError('Ground terms are nonempty arrays')
    f = nat(raw[0])
    if f not in signature or len(raw) != signature[f] + 1:
        raise ValueError('Unknown function symbol or incorrect arity')
    return (f, *(ground_term(t, signature) for t in raw[1:]))


def substitute(term, environment):
    if type(term) is int:
        return environment[term]
    return (term[0], *(substitute(t, environment) for t in term[1:]))


@dataclass
class Clauses:
    signature: dict = field(default_factory=lambda: {0: 0})
    clauses: list = field(default_factory=list)
    clause_variables: list = field(default_factory=list)
    next_variable: int = 0

    def add(self, raw):
        """Append clauses equisatisfiable with one closed first-order sentence.

        Fresh symbols are global to this object. NNF conversion, Skolemization,
        and CNF distribution are fused but governed by separate standard laws.
        Existential witnesses depend on every universal variable in their scope.
        No binder is moved by textual substitution, so shadowing is explicit.
        """
        formula = syntax.parse(raw)
        if syntax.free(formula):
            raise ValueError('Clausification requires a closed sentence')

        def visit(f, positive, environment, universals):
            op = f[0]
            if op in ('T', 'B'):
                return [] if positive == (op == 'T') else [()]
            if op == 'E':
                return [((positive, environment[f[1]], environment[f[2]]),)]
            if op == 'I':
                left = visit(f[1], not positive, environment, universals)
                right = visit(f[2], positive, environment, universals)
                return [a + b for a in left for b in right] if positive else left + right
            if op != 'A':
                raise ValueError('Unsupported logical constructor')
            if positive:
                term = self.next_variable
                self.next_variable += 1
                body_universals = universals + (term,)
            else:
                symbol = len(self.signature)
                self.signature[symbol] = len(universals)
                term = (symbol, *universals)
                body_universals = universals
            return visit(f[2], positive, environment | {f[1]: term}, body_universals)

        for clause in visit(formula, True, {}, ()):
            used = set().union(*(variables(t) for literal in clause for t in literal[1:]))
            self.clauses.append(clause)
            self.clause_variables.append(tuple(sorted(used)))
        return self

    def instance(self, source, arguments):
        source = nat(source)
        if source >= len(self.clauses):
            raise ValueError('Source clause is out of range')
        if not isinstance(arguments, list) or len(arguments) != len(self.clause_variables[source]):
            raise ValueError('Incorrect substitution length')
        terms = [ground_term(t, self.signature) for t in arguments]
        env = dict(zip(self.clause_variables[source], terms, strict=True))
        return tuple((sign, substitute(a, env), substitute(b, env))
                     for sign, a, b in self.clauses[source])


def compile_psc(matrices):
    if not isinstance(matrices, list):
        raise ValueError('The matrices must form a list')
    result = Clauses()
    for matrix in matrices:
        sentence = syntax.closure(syntax.parse(matrix), seed='subset', mixed=False)
        result.add(sentence)
    return result


def complementary(a, b):
    return a[0] != b[0] and a[1:] == b[1:]


def check_trace(package, trace):
    """Check preorder instructions with automatic depth-first backtracking.

    ['e', clause_index, ground_arguments] branches over that ground instance.
    ['c', ancestor_index] closes the branch against its newest literal.
    Every sibling must close. An empty clause closes immediately. Trailing
    instructions, unfinished branches, and malformed certificates are rejected.
    The generic interface accepts supplied clauses for tests; PSC callers must
    use check_certificate, which generates every nonlogical axiom itself.
    """
    if not isinstance(trace, list):
        raise ValueError('The instruction trace must be a list')
    trail, frames = [], []
    done = False
    extensions = closures = maximum_trail = maximum_frames = 0

    def advance():
        if not frames:
            trail.clear()
            return True
        depth, clause, index = frames.pop()
        del trail[depth:]
        if index + 1 < len(clause):
            frames.append((depth, clause, index + 1))
        trail.append(clause[index])
        return False

    for instruction in trace:
        if done:
            raise ValueError('Instructions occur after complete closure')
        if not isinstance(instruction, list) or not instruction:
            raise ValueError('An instruction must be a nonempty array')
        if instruction[0] == 'e' and len(instruction) == 3:
            clause = package.instance(instruction[1], instruction[2])
            extensions += 1
            if clause:
                if len(clause) > 1:
                    frames.append((len(trail), clause, 1))
                trail.append(clause[0])
            else:
                closures += 1
                done = advance()
        elif instruction[0] == 'c' and len(instruction) == 2:
            index = nat(instruction[1])
            if index >= len(trail) - 1 or not complementary(trail[index], trail[-1]):
                raise ValueError('The newest literal does not close against that ancestor')
            closures += 1
            done = advance()
        else:
            raise ValueError('Unknown instruction or incorrect arity')
        maximum_trail = max(maximum_trail, len(trail))
        maximum_frames = max(maximum_frames, len(frames))
    if not done:
        raise ValueError('The trace leaves an unfinished branch')
    return {'valid': True, 'extensions': extensions, 'closed_branches': closures,
            'maximum_trail': maximum_trail, 'maximum_branch_frames': maximum_frames}


def check_certificate(certificate):
    if not isinstance(certificate, dict) or set(certificate) != {'matrices', 'trace'}:
        raise ValueError('Only matrices and a refutation trace are admitted')
    package = compile_psc(certificate['matrices'])
    result = check_trace(package, certificate['trace'])
    return result | {'refutation': True, 'schema_instances': len(certificate['matrices']),
                     'clauses': len(package.clauses), 'Skolem_symbols': len(package.signature)-1}


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (isqrt(8*n + 1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b


def decode_list(n):
    result = []
    while n:
        head, n = unpair(n-1)
        result.append(head)
    return result


def encode_list(values):
    result = 0
    for value in reversed(values):
        result = 1 + pair(value, result)
    return result


def decode_matrix(n):
    if n == 0:
        return ['B']
    q, tag = divmod(n-1, 3)
    a, b = unpair(q)
    if tag == 0:
        return ['E', a, b]
    if tag == 1:
        return ['I', decode_matrix(a), decode_matrix(b)]
    return ['A', a, decode_matrix(b)]


def encode_matrix(f):
    if f[0] == 'B':
        return 0
    if f[0] == 'E':
        return 1 + 3*pair(f[1], f[2])
    if f[0] == 'I':
        return 2 + 3*pair(encode_matrix(f[1]), encode_matrix(f[2]))
    if f[0] == 'A':
        return 3 + 3*pair(f[1], encode_matrix(f[2]))
    raise ValueError('The enumerated syntax is bottom, membership, implication, universal')


def decode_term(n):
    symbol, args = unpair(n)
    return [symbol, *(decode_term(a) for a in decode_list(args))]


def encode_term(t):
    return pair(t[0], encode_list([encode_term(a) for a in t[1:]]))


def decode_instruction(n):
    if n % 2 == 0:
        return ['c', n//2]
    source, args = unpair(n//2)
    return ['e', source, [decode_term(a) for a in decode_list(args)]]


def encode_instruction(i):
    if i[0] == 'c':
        return 2*i[1]
    return 1 + 2*pair(i[1], encode_list([encode_term(t) for t in i[2]]))


def decode_certificate(n):
    matrices, trace = unpair(n)
    return {'matrices': [decode_matrix(m) for m in decode_list(matrices)],
            'trace': [decode_instruction(i) for i in decode_list(trace)]}


def encode_certificate(c):
    if not isinstance(c, dict) or set(c) != {'matrices', 'trace'}:
        raise ValueError('Refutations have exactly two fields')
    return pair(encode_list([encode_matrix(m) for m in c['matrices']]),
                encode_list([encode_instruction(i) for i in c['trace']]))


def accepts(n):
    nat(n)
    try:
        return check_certificate(decode_certificate(n))['valid']
    except (ValueError, KeyError, IndexError):
        return False


def search():
    """With ideal unbounded finite storage, return iff Q_PSC is inconsistent."""
    for code in itertools.count():
        if accepts(code):
            return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', type=Path)
    group.add_argument('--prefix', type=int)
    group.add_argument('--search', action='store_true')
    args = parser.parse_args()
    if args.check is not None:
        print(json.dumps(check_certificate(json.loads(args.check.read_text())), indent=2))
    elif args.prefix is not None:
        nat(args.prefix)
        found = next((n for n in range(args.prefix) if accepts(n)), None)
        print(json.dumps({'diagnostic_prefix': args.prefix, 'refutation_code': found,
                          'scope': 'A finite failed search proves no consistency statement'}))
    else:
        print(json.dumps({'refutation_code': search()}))


if __name__ == '__main__':
    main()
