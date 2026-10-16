#!/usr/bin/env python3
"""Focused executable checks for qnand.py; none proves Con(EPSC) or Con(ZFC)."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import random

import qnand as q


class FiniteEvaluator:
    """Test-only semantic evaluator, memoized by actually occurring variables.

    The checker does not use this class or compute free-variable supports.
    """
    def __init__(self, arena, domain, mask):
        self.a, self.domain, self.mask = arena, tuple(domain), mask
        self.size = len(self.domain)
        self.support, self.memo = [], {}
        for tag, x, y in arena.nodes:
            self.support.append(tuple(sorted({i - 1 for child in (x, y)
                                              for i in self.support[child] if i}
                                             if tag else {x, y})))

    def rel(self, x, y):
        return bool(self.mask & (1 << (self.size * x + y)))

    def eval(self, root, env=()):
        key = (root, tuple(env[i] for i in self.support[root]))
        if key in self.memo:
            return self.memo[key]
        tag, x, y = self.a.nodes[root]
        if tag:
            out = all(not (self.eval(x, (v,) + env) and self.eval(y, (v,) + env))
                      for v in self.domain)
        else:
            out = self.rel(env[x], env[y])
        self.memo[key] = out
        return out


def expect_invalid(f):
    try:
        f()
    except q.Invalid:
        return
    raise AssertionError("invalid certificate was accepted")


def direct_epsc(evaluator, matrix, params):
    """Evaluate the source14 EPSC definition directly over a finite graph.

    SB(rho) -> exists C [forall x,y ((empty(x) or x in C) and rho(x,y)
    -> y in C) and forall y(y in C -> exists x rho(x,y))].
    No quantified-NAND wrapper nodes are inspected here.
    """
    d, r = evaluator.domain, evaluator.rel
    def rho(x, y):
        return evaluator.eval(matrix, (x, y) + params)
    def subset(y, b):
        return all(not r(z, y) or r(z, b) for z in d)
    bounded = all(any(all(not rho(x, y) or subset(y, b) for y in d)
                      for b in d) for x in d)
    if not bounded:
        return True
    def good(c):
        closed = all(not ((all(not r(z, x) for z in d) or r(x, c)) and rho(x, y))
                     or r(y, c) for x in d for y in d)
        support = all(not r(y, c) or any(rho(x, y) for x in d) for y in d)
        return closed and support
    return any(good(c) for c in d)


def run():
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not run with -O")
    counts = {}
    # No special zero exception: exact natural-number syntax bijection.
    for n in range(10000):
        arena = q.Arena()
        root = arena.decode(n)
        assert arena.encode(root) == n
    counts["numeric_codec_roundtrips"] = 10000

    # Strongly focused index collisions, free/bound distinctions, and lifts.
    rng = random.Random(20261016)
    rebase_cases = shift_cases = raw_eval_cases = 0
    for n in range(160):
        a = q.Arena()
        p = a.decode(n)
        width = max(2, a.need[p])
        mapping = tuple(rng.randrange(3) for _ in range(width))
        transformed = a.transform(p, mapping)
        shifted = a.shift(p)
        for mask in range(16):
            ev = FiniteEvaluator(a, range(2), mask)
            for env in itertools.product(range(2), repeat=3):
                source = tuple(env[i] for i in mapping)
                assert ev.eval(transformed, env) == ev.eval(p, source)
                rebase_cases += 1
                for dummy in range(2):
                    assert ev.eval(shifted, (dummy,) + source) == ev.eval(p, source)
                    shift_cases += 1
            if n < 20:
                source = (0,) * width
                assert ev.eval(p, source) == q.evaluate(a, p, range(2), ev.rel, source)
                raw_eval_cases += 1
    counts.update(rebase_semantic_cases=rebase_cases,
                  shift_semantic_cases=shift_cases,
                  independent_raw_evaluator_cases=raw_eval_cases)

    # The mathematical EPSC wrapper, including parameter closure, is checked
    # against independent finite quantification, not against its own AST.
    epsc_cases = 0
    codes = []
    for n in range(500):
        a = q.Arena()
        matrix = a.decode(n)
        if a.need[matrix] > 3:
            continue
        codes.append(n)
        root = q.epsc(a, matrix)
        assert a.need[root] == 0
        width = max(2, a.need[matrix])
        for size in (1, 2):
            for mask in range(1 << (size * size)):
                ev = FiniteEvaluator(a, range(size), mask)
                expected = all(direct_epsc(ev, matrix, params) for params in
                               itertools.product(range(size), repeat=width - 2))
                assert ev.eval(root) == expected, (n, size, mask)
                epsc_cases += 1
    counts.update(epsc_matrices=len(codes), epsc_graph_comparisons=epsc_cases)

    # Every below-scope formula has an explicit finite identity certificate.
    identity_count = 0
    for n in range(1000):
        a = q.Arena()
        p = a.decode(n)
        env = (0,) * a.need[p]
        stream = q.identity_actions(a, p, 0, 1, 2)
        result = q.check_tree(a, [q.Entry(True, p, env), q.Entry(False, p, env)], stream)
        assert result["closed_branches"] >= 1
        identity_count += 1
    counts["identity_certificates"] = identity_count

    # Genuine cross-variable instantiation: forall x R(x,b), not R(a,b).
    a = q.Arena()
    atom = a.rel(0, 1)
    universal = a.all(atom)
    roots = [q.Entry(True, universal, (0,)), q.Entry(False, atom, (1, 0))]
    ui = [0, 1, 2, 3, 1, 2, 3, 1]
    ui_result = q.check_tree(a, roots, ui)
    assert ui_result["closed_branches"] == 2

    # Identification of both object slots: forall x,y R(x,y), not R(z,z).
    # Each all() is Q(neg(body),neg(body)); the following recursive producer
    # deliberately instantiates both distinct bound variables with parameter0.
    a2 = q.Arena()
    atom2 = a2.rel(1, 0)
    universals = a2.all(a2.all(atom2))
    false_atom = a2.rel(0, 0)
    roots2 = [q.Entry(True, universals), q.Entry(False, false_atom, (0,))]
    def universal_chain(index, length, layers):
        # +all: fork -neg(body), then -neg allocates its vacuous fresh name.
        # The actual +body starts at length+1, with the original parameter0.
        if layers == 0:
            return [index, 1]
        child = ([length] + universal_chain(length + 1, length + 3, layers - 1))
        return [index, 0] + child + child
    id_stream = universal_chain(0, 2, 2)
    identification_result = q.check_tree(a2, roots2, id_stream)
    assert identification_result["closed_branches"] == 4

    # Reject a forged witness that would need a fresh existential name to be
    # identified with the old parameter0: exists x R(x,x), not R(0,0) is SAT.
    a3 = q.Arena()
    p = a3.rel(0, 0)
    existential = a3.ex(p)
    sat_roots = [q.Entry(True, existential), q.Entry(False, p, (0,))]
    expect_invalid(lambda: q.check_tree(a3, sat_roots, [0, 0, 2, 3, 1]))
    ev = FiniteEvaluator(a3, range(2), 1 << 3)
    assert ev.eval(existential) and not ev.eval(p, (0,))

    # These exact boundary mutations should all be rejected.
    bad_checks = [
        lambda: q.check_tree(a, roots, [0, 2]),  # m=2, so parameter2 is unknown
        lambda: q.check_tree(a, roots, ui[:5]),  # only the first fork was closed
        lambda: q.check_tree(a, roots, ui + [0]),
        lambda: q.check_tree(a, roots, [99]),
        lambda: q.check_tree(a, roots, [True]),
        lambda: q.check_tree(a, roots, [-1]),
        lambda: q.check_tree(a, [q.Entry(True, atom)], [0, 0]),
        lambda: q.check_tree(a, [q.Entry(True, atom, (0, 1)),
                                 q.Entry(False, atom, (1, 0))], [0, 1]),
        lambda: q.check_tree(a, [q.Entry(True, atom, (0, 1)),
                                 q.Entry(True, atom, (0, 1))], [0, 1]),
        lambda: q.decode_bits("001"),
        lambda: q.decode_bits("10"),
        lambda: q.decode_bits("x"),
    ]
    for f in bad_checks:
        expect_invalid(f)
    counts.update(cross_variable_ui=ui_result,
                  variable_identification=identification_result,
                  invalid_certificate_regressions=len(bad_checks) + 1)

    # Wire roundtrips do not validate refutations; no theorem target is present.
    for _ in range(1000):
        matrices = [rng.randrange(8) for _ in range(rng.randrange(5))]
        actions = [rng.randrange(8) for _ in range(rng.randrange(20))]
        assert q.decode_bits(q.encode_bits(matrices, actions)) == (matrices, actions)
    counts["wire_roundtrips"] = 1000
    counts["diagnostic_candidate_prefix"] = 1000
    assert not any(q.accepts(bin(n)[3:]) for n in range(1, 1001))

    # Artifact metric for exactly the matrix R(0,1), with no size extrapolation.
    a4 = q.Arena()
    matrix = a4.decode(4)
    root = q.epsc(a4, matrix)
    reached, todo = set(), [root]
    while todo:
        p = todo.pop()
        if p in reached:
            continue
        reached.add(p)
        tag, x, y = a4.nodes[p]
        if tag:
            todo.extend((x, y))
    counts["epsc_R01_representation"] = {
        "input_matrix_numeric_code": 4,
        "reachable_nodes": len(reached),
        "reachable_compound_nodes": sum(a4.nodes[p][0] for p in reached),
        "reachable_atom_nodes": sum(not a4.nodes[p][0] for p in reached),
        "allocated_reference_builder_nodes": len(a4.nodes),
        "scope_requirement": a4.need[root],
    }
    counts["status"] = "finite tests only; no certified TM, state bound, or consistency claim"
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = run()
    text = json.dumps(results, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
