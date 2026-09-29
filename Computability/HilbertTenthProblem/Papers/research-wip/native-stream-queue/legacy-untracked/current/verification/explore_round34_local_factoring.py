#!/usr/bin/env python3
"""Bounded local algebra search; candidates are not certificate claims.

Only nodes with one consumer are expanded.  Shared nodes remain atomic,
so a proposed saving cannot silently delete a shared computation.
"""
from collections import Counter
import sympy as sp
import round34_1980_factored_mask_certificate as certificate

definitions = {row[0]: row[1:] for row in certificate.SCHEDULE}
uses = Counter(x for _, _, left, right in certificate.SCHEDULE
               for x in (left, right) if isinstance(x, str))
uses.update(x for pair in certificate.EQUALITIES for x in pair)


def region(name, depth, force=False):
    if not isinstance(name, str):
        return sp.Integer(name), set()
    if depth == 0 or name not in definitions or (not force and uses[name] != 1):
        return sp.Symbol(name), set()
    operation, left, right = definitions[name]
    a, sa = region(left, depth-1)
    b, sb = region(right, depth-1)
    value = a+b if operation == '+' else a-b if operation == '-' else a*b
    return value, sa | sb | {name}


def arithmetic_cost(expression):
    seen = set()

    def visit(e):
        if e.is_Atom or e in seen:
            return 0
        seen.add(e)
        if e.is_Add:
            terms = [(-x if x.could_extract_minus_sign() else x) for x in e.args]
            return len(terms)-1 + sum(visit(x) for x in terms)
        if e.is_Mul:
            coefficient, rest = e.as_coeff_Mul()
            if coefficient == -1:
                return 1+visit(rest)
            return len(e.args)-1 + sum(visit(x) for x in e.args)
        if e.is_Pow and e.exp.is_Integer and e.exp > 0:
            power = int(e.exp)
            return visit(e.base) + power.bit_length()-1 + power.bit_count()-1
        raise ValueError(e)

    return visit(expression)


def search():
    findings = []
    unique = set()
    for target, *_ in certificate.SCHEDULE:
        for depth in range(1, 8):
            expression, nodes = region(target, depth, force=True)
            if not 2 <= len(nodes) <= 22:
                continue
            expanded = sp.expand(expression)
            candidates = [sp.factor(expression), sp.factor_terms(expression), expanded]
            candidates += [sp.collect(expanded, symbol)
                           for symbol in sorted(expression.free_symbols, key=str)]
            for candidate in candidates:
                signature = (target, sp.sstr(candidate), tuple(sorted(nodes)))
                if signature in unique:
                    continue
                unique.add(signature)
                cost = arithmetic_cost(candidate)
                if cost < len(nodes):
                    assert sp.expand(candidate-expression) == 0
                    findings.append((target, len(nodes), cost,
                                     sp.sstr(candidate), sorted(nodes)))
    for finding in findings:
        print(finding)
    print('Candidate count:', len(findings))
    print('Scope: bounded syntax search, not an optimality proof or verified replacement.')


if __name__ == '__main__':
    search()
