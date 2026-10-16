#!/usr/bin/env python3
"""Independent semantic and adversarial regressions for closure_tableau.

Finite tests check the transcription; proofs of the unbounded claims are
in the report. This script needs only the Python standard library.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
import unittest

import closure_tableau as c


def direct_matrix(f, relation, env):
    """Independent ordinary named-variable semantics (no Entry/resolve)."""
    op = f[0]
    if op == "T": return True
    if op == "B": return False
    if op == "R": return bool(relation[env.get(f[2], 0)] & (1 << env.get(f[1], 0)))
    if op == "I": return not direct_matrix(f[1], relation, env) or direct_matrix(f[2], relation, env)
    if op == "A":
        return all(direct_matrix(f[2], relation, env | {f[1]: v}) for v in range(len(relation)))
    raise ValueError(op)


def direct_epsc(matrix, relation, parameters):
    n = len(relation)
    mem = lambda x, y: bool(relation[y] & (1 << x))
    sub = lambda x, y: all(not mem(z, x) or mem(z, y) for z in range(n))
    rho = [[direct_matrix(matrix, relation, parameters | {0: x, 1: y})
            for y in range(n)] for x in range(n)]
    locally_bounded = all(any(all(not rho[x][y] or sub(y, b)
                                     for y in range(n))
                                 for b in range(n)) for x in range(n))
    if not locally_bounded: return True
    for hull in range(n):
        forward = all(not (relation[x] == 0 or mem(x, hull))
                      or all(not rho[x][y] or mem(y, hull) for y in range(n))
                      for x in range(n))
        support = all(not mem(y, hull) or any(rho[x][y] for x in range(n))
                      for y in range(n))
        if forward and support: return True
    return False


def eager_schema(matrix):
    """Differential oracle: build the ordinary capture-free expanded formula.

    Only this test oracle renames matrix syntax. It is absent from the
    acceptance/search implementation.
    """
    start = 1 + max({0, 1} | c.all_labels(matrix))
    roles = {i: start + i for i in range(5)}

    def rename_free(f, substitutions):
        op = f[0]
        if op == "R": return c.R(substitutions.get(f[1], f[1]), substitutions.get(f[2], f[2]))
        if op == "I": return c.I(rename_free(f[1], substitutions), rename_free(f[2], substitutions))
        if op == "A":
            return c.A(f[1], rename_free(f[2], {k: v for k, v in substitutions.items() if k != f[1]}))
        return f

    rho = rename_free(matrix, {0: roles[0], 1: roles[1]})

    def expand(f):
        op = f[0]
        if op == "H": return rho
        if op == "R": return c.R(roles[f[1]], roles[f[2]])
        if op == "I": return c.I(expand(f[1]), expand(f[2]))
        if op == "A": return c.A(roles[f[1]], expand(f[2]))
        return f
    return expand(c.EPSC)


MATRICES = [c.BOTTOM, c.TRUTH, c.R(0, 1), c.R(0, 2),
            c.A(0, c.R(0, 1)), c.A(1, c.R(0, 1)),
            c.I(c.R(0, 2), c.A(2, c.R(2, 1))),
            c.A(0, c.I(c.R(0, 2), c.R(1, 0))),
            c.A(2, c.I(c.R(0, 2), c.A(0, c.R(0, 1))))]


def ui_example():
    f = c.A(1, c.A(2, c.I(c.A(0, c.R(0, 1)), c.R(2, 1))))
    p = ["all", 0, ["all", 1, ["imp", 2, ["all", 3, 2, ["close", 5, 4]]]]]
    return {"theorem": f, "proof": p}


def schema_example(matrix):
    """Prove the generated schema itself, including free parameter closure."""
    formula = eager_schema(matrix)
    labels = sorted(c.free_labels(matrix) - {0, 1})
    theorem = formula
    for k in reversed(labels): theorem = c.A(k, theorem)
    used = frozenset({0})
    negative = c.Entry(False, theorem)
    prefix = []
    parameters = []
    for label in labels:
        index = len(prefix)
        k = max(used) + 1
        used = used | {k}
        parameters.append((label, k))
        prefix.append(index)
        negative = negative.instantiate(k)
    positive = c.schema_entry(c.encode(matrix), parameters)
    ni = len(prefix)
    pi = ni + 1
    identity = c.identity_proof(positive, negative, pi, ni, pi + 1, used)
    proof = ["axiom", c.encode(matrix), parameters, identity]
    for index in reversed(prefix): proof = ["all", index, proof]
    return {"theorem": theorem, "proof": proof}


class ReferenceTests(unittest.TestCase):
    def test_unique_bottom_and_low_codes(self):
        self.assertEqual(c.decode(0), c.TRUTH)
        self.assertEqual(c.decode(1), c.BOTTOM)
        self.assertEqual(c.decode(4), c.R(0, 0))
        self.assertEqual(c.decode(2), c.A(0, c.TRUTH))
        self.assertNotEqual(c.decode(7), c.BOTTOM)

    def test_cross_variable_ui(self):
        e = ui_example()
        self.assertTrue(c.check_theorem(e["theorem"], e["proof"])["valid"])

    def test_wrong_ui_rejected(self):
        e = ui_example()
        bad = ["all", 0, ["all", 1, ["imp", 2, ["all", 3, 1, ["close", 5, 4]]]]]
        with self.assertRaises(ValueError): c.check_theorem(e["theorem"], bad)

    def test_bottom_truth_signs(self):
        self.assertTrue(c.check_theorem(c.TRUTH, ["constant", 0])["valid"])
        with self.assertRaises(ValueError): c.check_refutation(["constant", 0])
        with self.assertRaises(ValueError):
            c.check_tree((c.Entry(True, c.TRUTH),), ["constant", 0])

    def test_eigenvariable_reuse_rejected(self):
        roots = (c.Entry(True, c.R(0, 0), ((0, 1),)), c.Entry(False, c.A(0, c.R(0, 0))))
        with self.assertRaises(ValueError): c.check_tree(roots, ["all", 1, ["close", 0, 2]])
        with self.assertRaises(ValueError): c.check_tree(roots, ["all", 1, 1, ["close", 0, 2]])

    def test_private_holes_and_arbitrary_axioms_rejected(self):
        with self.assertRaises(ValueError): c.parse_formula(["H"])
        with self.assertRaises(ValueError): c.encode(c.HOLE)
        with self.assertRaises(ValueError): c.check_refutation(["axiom", -1, [], ["constant", 1]])

    def test_parameter_integrity(self):
        for params in [[(0, 1)], [(1, 2)], [(2, 1), (2, 3)], [(True, 2)], [(2, -1)]]:
            with self.assertRaises(ValueError): c.schema_entry(1, params)

    def test_schema_identity_with_shadowing(self):
        for m in MATRICES:
            e = schema_example(m)
            self.assertTrue(c.check_theorem(e["theorem"], e["proof"])["valid"])

    def test_public_refutation_target_fixed(self):
        e = ui_example()
        with self.assertRaises(ValueError): c.check_refutation(e["proof"])

    def test_small_proof_codec(self):
        for n in range(5000):
            self.assertEqual(c.proof_encode(c.proof_decode(n)), n)

    def test_numeric_ui_roundtrip(self):
        p = ui_example()["proof"]
        q = c.proof_decode(c.proof_encode(p))
        self.assertEqual(q, p)

    def test_malformed_proof_arities(self):
        for p in [[], ["close", 0], ["imp", 0], ["all", 0, []], ["close", True, 0]]:
            with self.assertRaises(ValueError): c.check_refutation(p)


def semantic_audit(max_domain=3):
    comparisons = 0
    sizes = {}
    decoded = [c.decode(c.encode(m)) for m in MATRICES]
    entries = [c.schema_entry(c.encode(m), [(2, 2)]) for m in MATRICES]
    eager = [eager_schema(m) for m in decoded]
    for n in range(1, max_domain + 1):
        before = comparisons
        for relation in itertools.product(range(1 << n), repeat=n):
            for value in range(n):
                params = {2: value}
                assignment = {0: 0, 2: value}
                for m, lazy, ordinary in zip(decoded, entries, eager):
                    actual = c.evaluate(lazy, relation, assignment)
                    wanted = direct_epsc(m, relation, params)
                    expanded = direct_matrix(ordinary, relation, params)
                    if actual != wanted or actual != expanded:
                        raise AssertionError((n, relation, value, m, actual, wanted, expanded))
                    comparisons += 1
        sizes[str(n)] = comparisons - before
    return {"matrix_families": len(MATRICES), "relations": sum(2 ** (n*n) for n in range(1, max_domain+1)),
            "three_way_semantic_comparisons": comparisons, "by_domain_size": sizes,
            "includes_bound_0_1_shadowing_and_parameter_2_shadowing": True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    ap.add_argument("--examples", type=Path)
    ap.add_argument("--max-domain", type=int, default=3)
    args = ap.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ReferenceTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    if not result.wasSuccessful(): raise SystemExit(1)
    for n in range(100000):
        f = c.decode(n)
        if c.encode(f) != n or any(label >= n for label in c.all_labels(f)):
            raise AssertionError((n, f))
    evidence = {"status": "finite transcription checks; unbounded proofs are in report",
                "unit_tests": result.testsRun, "unit_failures": 0,
                "exact_formula_code_roundtrips": 100000,
                "numeric_proof_roundtrips": 5000,
                "semantics": semantic_audit(args.max_domain),
                "search_prefix": c.search(10000),
                "ui_certificate": c.check_theorem(ui_example()["theorem"], ui_example()["proof"])}
    if args.examples:
        args.examples.mkdir(parents=True, exist_ok=True)
        examples = {"cross_variable_ui.json": ui_example(),
                    "epsc_shadowed_parameter.json": schema_example(MATRICES[7]),
                    "truth.json": {"theorem": c.TRUTH, "proof": ["constant", 0]}}
        for name, example in examples.items():
            (args.examples / name).write_text(json.dumps(example, indent=2) + "\n")
    if args.output:
        args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, indent=2, sort_keys=True))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O/-OO: the regression checks require assertions")
    main()
