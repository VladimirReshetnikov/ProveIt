#!/usr/bin/env python3
"""Independent literal formula and total-decoder interface audit for seed+G.

No source-generator or predecessor verification modules are imported.  The
expressions are independently transcribed from the mathematical specification.
This verifies the emitter receipt's target ASTs and the receipt/source hash
binding.  Register execution is the separate source certificate's obligation.
"""
import argparse
import hashlib
import json
from pathlib import Path


def frozen(value):
    return tuple(map(frozen, value)) if isinstance(value, list) else value


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lower(node):
    """Monotone numeric lower bound, saturated at 2."""
    if not isinstance(node, tuple):
        return min(node, 2) if isinstance(node, int) else 0
    op, x, y = node
    x, y = lower(x), lower(y)
    pair = (x + y) * (x + y + 1) // 2 + y
    return min(2, 4 * pair + {"I": 0, "R": 1, "Q": 2, "E": 3}[op])


def audit_decoder(expression, gate):
    counts = {"negations": 0, "implications": 0, "quantifiers": 0,
              "memberships": 0, "equalities": 0, "matrices": 0}

    def different_from_one(node):
        if not isinstance(node, tuple):
            return isinstance(node, int) and node != 1
        op, x, y = node
        if op != "R" or lower(x) > 0 or lower(y) > 0:
            return True
        return gate and ((x == "c" and y in ("a", "b")) or
                         (y == "c" and x in ("a", "b")))

    def visit(node):
        if not isinstance(node, tuple):
            assert node == "c", ("unknown matrix", node)
            counts["matrices"] += 1
            return
        op, x, y = node
        if op == "I":
            if y == 1:
                counts["negations"] += 1
                visit(x)
            else:
                assert different_from_one(y), ("unproved consequent!=1", node)
                assert lower(x) > 0 or lower(y) > 0, ("possible I(0,0)", node)
                counts["implications"] += 1
                visit(x)
                visit(y)
        elif op == "Q":
            counts["quantifiers"] += 1
            # Its first argument is a numerical label, not a formula position.
            visit(y)
        else:
            assert op in ("R", "E")
            counts["memberships" if op == "R" else "equalities"] += 1

    visit(expression)
    assert lower(expression) > 1
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_text())
    assert receipt["status"] == "EXACT_COMBINED_SOURCE_AND_ALL_NATURAL_EMITTER_PASS"
    assert receipt["source_sha256"] == digest(args.source)
    i = lambda x, y: ("I", x, y)
    r = lambda x, y: ("R", x, y)
    q = lambda x, y: ("Q", x, y)
    e = lambda x, y: ("E", x, y)
    n = lambda x: i(x, 1)
    membership = r("b", "c")
    subset = q("c", i(r("c", "a"), r("c", "b")))
    request = q("b", i("c", n(q("b", i("c", n(membership))))))
    closure = q("b", i(membership, n(q("a", i("c", n(q("a", i(subset, request))))))))
    vacuity = i(r("a", "b"), q("c", r("a", "b")))
    helper = i(e("a", "b"), q(r("a", "b"), e("a", "b")))
    tail = q("c", i(closure, n(request)))
    old_bundle = n(i(vacuity, i(helper, tail)))
    new_bundle = n(i(vacuity, tail))
    old_row = i(e("c", "a"), i(e("c", "b"), e("a", "b")))
    new_row = i(e("c", "a"), i(e("c", "b"), q(r("a", "b"), e("a", "b"))))
    for group, before, after in (("bundle", old_bundle, new_bundle),
                                 ("row", old_row, new_row)):
        assert frozen(receipt[group]["old_expression"]) == before
        assert frozen(receipt[group]["new_expression"]) == after
    checks = {
        "old_seed_bundle": audit_decoder(old_bundle, True),
        "new_seed_bundle": audit_decoder(new_bundle, True),
        "old_equality_row": audit_decoder(old_row, False),
        "new_G_row": audit_decoder(new_row, False),
    }
    result = {
        "status": "INDEPENDENT_LITERAL_FORMULAS_AND_UNIFORM_DECODER_PASS",
        "emitter_receipt_sha256": digest(args.receipt),
        "source_sha256": digest(args.source),
        "bundle_gate": "c != a and c != b",
        "G_row_gate": "none: every triple",
        "literal_specification_equal": True,
        "checks": checks,
        "scope": "Independent exact AST transcription, source hash binding, and uniform native-decoder constructor side conditions. Reuses the pinned D constructor lemmas. No source-generator imports; no bounded enumeration of labels; does not by itself prove register execution, row coverage, consistency calibration, or binary runtime.",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
