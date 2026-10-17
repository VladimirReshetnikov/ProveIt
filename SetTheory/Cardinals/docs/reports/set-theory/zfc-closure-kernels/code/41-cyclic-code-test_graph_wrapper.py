#!/usr/bin/env python3
"""Finite checks of the membership-wrapper substitution lemma.

The tests include arbitrary, non-extensional ambient membership graphs.
They establish finite regression evidence, not any consistency statement.
"""
import json
from itertools import product
from pathlib import Path
import sys

from graph_wrapper import (All, And, Eq, Ex, Fresh, Iff, Imp, Not, Or, Rel,
                           evaluate, free, induced_relation, labels, pack,
                           relativize, size, tree)


def run():
    open_formulas = [Eq(0, 1), Rel(0, 1), Not(Rel(1, 0)),
                     Imp(Rel(0, 1), Eq(0, 1)),
                     Ex(0, And(Rel(0, 1), Not(Eq(0, 1)))),
                     All(0, Or(Rel(0, 1), Not(Rel(1, 0)))),
                     Ex(0, All(1, Imp(Rel(0, 1), Eq(0, 1))))]
    sentences = [All(0, All(1, Eq(0, 1))),
                 Ex(0, Rel(0, 0)),
                 All(0, Not(Rel(0, 0))),
                 All(0, Ex(1, Rel(0, 1))),
                 Ex(0, Ex(1, And(Not(Eq(0, 1)), Rel(0, 1))))]
    translations = [relativize(f, 2, 3, Fresh(4)) for f in open_formulas]
    sentence_translations = [relativize(f, 2, 3, Fresh(4)) for f in sentences]
    comparisons = 0
    structure_count = 0
    packed_comparisons = 0
    for n in (1, 2, 3):
        ambient = tuple(range(n))
        masks = range(1 << (n * n)) if n < 3 else range(0, 512, 11)
        for mask in masks:
            mem = {(x, y) for x in ambient for y in ambient
                   if mask & (1 << (x * n + y))}
            for d, e in product(ambient, repeat=2):
                domain = tuple(x for x in ambient if (x, d) in mem)
                if not domain:
                    continue
                structure_count += 1
                induced = induced_relation(domain, ambient, mem, e)
                for x, y in product(domain, repeat=2):
                    for f, translated in zip(open_formulas, translations):
                        expected = evaluate(f, domain, induced, {0: x, 1: y})
                        actual = evaluate(translated, ambient, mem,
                                          {0: x, 1: y, 2: d, 3: e})
                        if expected != actual:
                            raise AssertionError((n, mask, d, e, x, y, f))
                        comparisons += 1
                for f, translated in zip(sentences, sentence_translations):
                    if evaluate(f, domain, induced) != evaluate(
                            translated, ambient, mem, {2: d, 3: e}):
                        raise AssertionError((n, mask, d, e, f))
                    comparisons += 1
            if n < 3:
                # Check the outer existential wrapper, not just its body.
                for f in sentences:
                    expected = False
                    for d, e in product(ambient, repeat=2):
                        domain = tuple(x for x in ambient if (x, d) in mem)
                        if domain and evaluate(f, domain, induced_relation(
                                domain, ambient, mem, e)):
                            expected = True
                    if evaluate(pack([f]), ambient, mem) != expected:
                        raise AssertionError((n, mask, f, "outer wrapper"))
                    packed_comparisons += 1
    malformed = [[], ["eq", True, 0], ["rel", -1, 0], ["exists", 0],
                 ["or", ["eq", 0, 0]], ["unknown", 0],
                 ["exists", False, ["eq", 0, 0]]]
    for value in malformed:
        try:
            tree(value)
        except ValueError:
            pass
        else:
            raise AssertionError(("accepted malformed syntax", value))
    try:
        pack([Rel(0, 1)])
    except ValueError:
        pass
    else:
        raise AssertionError("accepted an open axiom")
    # Shadowing survives, while every new label is globally fresh.
    shadowed = All(0, Ex(0, Rel(0, 0)))
    packed = pack([shadowed])
    assert not free(packed)
    assert labels(shadowed) < labels(packed)
    examples = {"name": "Nonempty irreflexive relation with a successor",
                "status": "calibration example only; not NBG or ZFC",
                "axioms": [sentences[2], sentences[3]]}
    root = Path(__file__).resolve().parents[1]
    (root / "examples").mkdir(exist_ok=True)
    (root / "examples/finite_relation_theory.json").write_text(
        json.dumps(examples, indent=2) + "\n")
    result = {"passed": True,
              "scope": "finite syntax/semantics regressions; no consistency proof",
              "nonempty_induced_structures": structure_count,
              "formula_semantics_comparisons": comparisons,
              "outer_wrapper_comparisons": packed_comparisons,
              "malformed_inputs_rejected": len(malformed) + 1,
              "example_source_nodes": sum(size(f) for f in examples["axioms"]),
              "example_wrapper_nodes": size(pack(examples["axioms"]))}
    destination = Path(sys.argv[1]) if len(sys.argv) > 1 else root / "data/graph_wrapper_results.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
