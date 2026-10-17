#!/usr/bin/env python3
"""Generate a specified 14-sentence pure-membership class theory.

Source: Harvey M. Friedman, Simplified Axioms for Class Theory,
September 15, 2020, section 2 rows 1--7 and A--H.  M(x) is eliminated
by exists y R(x,y), and the resulting tautological Sets row is omitted.

This is a formalization of the intended axioms, with explicitly documented
typographical normalization, not an assertion of glyph-for-glyph agreement
with the PDF. It is NOT an expanded Andreka--Nemeti/modal target or a TM.

New generator: MIT-0. The source mathematical presentation is attributed.
When this file is adjacent to graph_wrapper.py, run python finite_nbg.py
OUTPUT.json. In the research scratch layout, set PYTHONPATH to its code dir.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from graph_wrapper import (All, And, Eq, Ex, Fresh, Iff, Imp, Not, Or, Rel,
                           free, labels, size, tree)


SOURCE = ("https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/"
          "2020/09/NBGAxioms091520.pdf")


def forall(vs, body):
    for x in reversed(vs):
        body = All(x, body)
    return body


class Builder:
    def __init__(self):
        self.fresh = Fresh(0)

    def var(self):
        return self.fresh.get()

    def vars(self, n):
        return tuple(self.var() for _ in range(n))

    def is_set(self, x):
        y = self.var()
        return Ex(y, Rel(x, y))

    def subset(self, a, b):
        x = self.var()
        return All(x, Imp(Rel(x, a), Rel(x, b)))

    def pair(self, p, a, b):
        x = self.var()
        return All(x, Iff(Rel(x, p), Or(Eq(x, a), Eq(x, b))))

    def union(self, u, a):
        x, y = self.vars(2)
        return All(x, Iff(Rel(x, u), Ex(y, And(Rel(y, a), Rel(x, y)))))

    def intersection(self, u, a, b):
        x = self.var()
        return All(x, Iff(Rel(x, u), And(Rel(x, a), Rel(x, b))))

    def pairwise_union(self, u, a, b):
        x = self.var()
        return All(x, Iff(Rel(x, u), Or(Rel(x, a), Rel(x, b))))

    def complement(self, c, a):
        x = self.var()
        return All(x, Iff(Rel(x, c), And(Not(Rel(x, a)), self.is_set(x))))

    def subset_union(self, a, b):
        x, y = self.vars(2)
        return All(x, Imp(Rel(x, a), Ex(y, And(Rel(y, b), Rel(x, y)))))


def construct():
    rows = []

    def add(source_row, name, formula, annotation):
        formula = tree(formula)
        if free(formula):
            raise AssertionError((source_row, "free labels", free(formula)))
        rows.append({"source_row": source_row, "name": name,
                     "annotation": annotation, "formula": formula,
                     "formula_nodes": size(formula),
                     "labels_used": len(labels(formula))})

    b = Builder()
    a, d, x = b.vars(3)
    add("2", "Extensionality",
        forall((a, d), Imp(All(x, Iff(Rel(x, a), Rel(x, d))), Eq(a, d))),
        "All classes are extensional; equality is native first-order equality.")

    b = Builder()
    a, d, p = b.vars(3)
    add("3", "Pairing",
        forall((a, d), Imp(And(b.is_set(a), b.is_set(d)),
                           Ex(p, And(b.is_set(p), b.pair(p, a, d))))),
        "Input classes and output pair are sets, using the expanded M definition.")

    b = Builder()
    a, u = b.vars(2)
    add("4", "Union",
        All(a, Imp(b.is_set(a), Ex(u, And(b.is_set(u), b.union(u, a))))),
        "Set union; corrects the wrong bound-variable index in the section 2 union abbreviation.")

    b = Builder()
    a, p, x = b.vars(3)
    add("5", "Power Set",
        All(a, Imp(b.is_set(a), Ex(p, And(b.is_set(p),
              All(x, Iff(Rel(x, p), b.subset(x, a))))))),
        "The subset profile ranges over every class x, with no added M(x) guard.")

    b = Builder()
    a, x, y, z = b.vars(4)
    add("6", "Infinity",
        Ex(a, And(b.is_set(a), And(Ex(x, Rel(x, a)),
              All(y, Imp(Rel(y, a), Ex(z, And(Rel(z, a), Rel(y, z)))))))),
        "A nonempty set has no membership-maximal element; outer scope follows the stated English axiom.")

    b = Builder()
    a, x, y, z = b.vars(4)
    add("7", "Class Foundation",
        All(a, Imp(Ex(x, Rel(x, a)),
                   Ex(y, And(Rel(y, a), All(z, Imp(Rel(z, a), Not(Rel(z, y)))))))),
        "Class-wide foundation; equivalent to the universal closure of the displayed free-premise implication.")

    b = Builder()
    a, d, c, u = b.vars(4)
    add("A", "Boolean class operations",
        forall((a, d), And(Ex(c, b.complement(c, a)),
                           Ex(u, b.pairwise_union(u, a, d)))),
        "One conjunctive row: independent complement and pairwise-union witnesses, with fresh names.")

    b = Builder()
    a, u = b.vars(2)
    add("B", "Class Union", All(a, Ex(u, b.union(u, a))),
        "No set guard on the input or output class.")

    b = Builder()
    a, d, c, z, x, y = b.vars(6)
    add("C", "Local Pairing",
        forall((a, d), Ex(c, All(z, Iff(Rel(z, c),
              Ex(x, And(Rel(x, a), Ex(y, And(Rel(y, d), b.pair(z, x, y))))))))),
        "Inputs to the local pair are members of the parameter classes; no extra sort guards are inserted.")

    b = Builder()
    a, c, z, x = b.vars(4)
    add("D", "Local Union",
        All(a, Ex(c, All(z, Iff(Rel(z, c),
              Ex(x, And(Rel(x, a), b.union(z, x))))))),
        "The class consists exactly of unions of members of the input class.")

    b = Builder()
    a, d, c, z, x, y = b.vars(6)
    add("E", "Local Intersection",
        forall((a, d), Ex(c, All(z, Iff(Rel(z, c),
              Ex(x, And(Rel(x, a), Ex(y, And(Rel(y, d),
                                          b.intersection(z, x, y))))))))),
        "The class consists exactly of pairwise intersections of input members.")

    b = Builder()
    a, c, x, u = b.vars(4)
    add("F", "Union Membership",
        All(a, Ex(c, All(x, Iff(Rel(x, c),
              Ex(u, And(Rel(u, a), b.union(u, x))))))),
        "No M(x) guard; use actual row F, not the mismatching Union Inclusion prose in Lemma 2.1.")

    b = Builder()
    c, z, x, y = b.vars(4)
    add("G", "Epsilon Class",
        Ex(c, All(z, Iff(Rel(z, c),
              Ex(x, Ex(y, And(b.pair(z, x, y), Rel(x, y))))))),
        "Witness x,y range over classes; the exact pair profile itself requires them to be elements when such z exists.")

    b = Builder()
    a, d, c = b.vars(3)
    add("H", "Capture",
        forall((a, d), Imp(And(b.is_set(d), b.subset_union(d, a)),
              Ex(c, And(b.is_set(c), And(b.subset(c, a),
                                        b.subset_union(d, c)))))),
        "For a set d contained in the union of class a, a set subclass c of a still covers d by its union.")

    assert [row["source_row"] for row in rows] == list("234567ABCDEFGH")
    assert len(rows) == 14
    return rows


def capture_fixture():
    """Finite HF witness to the source proof gap, and its tagged repair."""
    def union(a):
        return frozenset().union(*a)

    zero = frozenset()
    one = frozenset((zero,))
    two = frozenset((zero, one))
    a = two
    phi = ((zero, zero), (one, two))
    old_b = frozenset(frozenset((x, frozenset((x, y)))) for x, y in phi)
    old_c = frozenset((two,))
    assert old_c <= old_b and a <= union(old_c)
    old_bound = union(union(old_c))
    assert old_bound == one
    assert not any(x == one and y in old_bound for x, y in phi)
    tag = frozenset(z for z in union(a) if z not in z)
    assert tag == one and tag not in union(a)
    new_b = tuple(frozenset((x, frozenset((tag, y)))) for x, y in phi)
    covering = 0
    for mask in range(1 << len(new_b)):
        c = frozenset(q for i, q in enumerate(new_b) if mask & (1 << i))
        if a <= union(c):
            covering += 1
            bound = union(union(c))
            assert all(any(u == x and y in bound for u, y in phi) for x in a)
    return {"scope": "one finite proof-inference diagnostic, not an axiom countermodel",
            "A": "{0,1}", "phi": [[0, 0], [1, 2]],
            "old_C": "{{0,1}}", "old_double_union": "{0}",
            "old_C_covers_A": True, "old_C_collects_phi_witnesses": False,
            "failed_input": 1, "tag_b": 1,
            "tagged_covering_subclasses_checked": covering,
            "all_tagged_covers_collect": True}


def document():
    rows = construct()
    return {
        "name": "Friedman NBG* fourteen-sentence membership reduct (specified normalization)",
        "status": "finite first-order source target; full modal translation and binary machine absent",
        "source": {"author": "Harvey M. Friedman",
                   "title": "Simplified Axioms for Class Theory",
                   "date": "2020-09-15", "url": SOURCE,
                   "axiom_location": "section 2, inherited rows 1-7 plus A-H",
                   "equivalence_location": "Theorem 3.21"},
        "language": {"relation": "one binary R, interpreted as membership",
                     "equality": "native first-order equality",
                     "syntax_tags": ["eq", "rel", "not", "or", "exists"],
                     "domain": "nonempty, containing both sets and proper classes when present"},
        "normalization": {
            "set_predicate": "M(x) := exists y R(x,y), using fresh bound variables",
            "omitted_row": "1 Sets becomes a logical alpha-equivalence and is omitted",
            "universal_closure": "all formerly free axiom parameters are explicitly universally bound",
            "union_typo": "section 2 printed v2 in the union body is read as the quantified candidate element v(i+1)",
            "boolean_scope": "row A conjoins two independent existence assertions, with fresh witness names",
            "infinity_scope": "the set witness scopes over nonemptiness and the entire no-maximal-member property",
            "foundation_scope": "class nonemptiness is written as an existential antecedent",
            "choice": "No Choice axiom or global Choice is added",
            "literal_pdf_transcription": False},
        "source_proof_notes": [
            "Lemma 2.1 discusses Union Inclusion where row F is Union Membership; Lemma 3.1 discusses the actual membership form.",
            "Lemma 3.19's second negated existential in the equality case prints an implication; intended extensionality uses a conjunction with negated membership.",
            "Lemma 3.20's coded class A needs two successive Class Union operations to recover its selected members and possible tags; the printed single union is one level short.",
            "Theorem 3.21's displayed Collection coding has a coordinate-alias gap; use {x,{b,y}} with b not in union(A), rather than {x,{x,y}}. Capture then cannot cover an element of A through the second component. This changes no axiom.",
            "The generator follows intended axioms; it does not serialize or independently formalize the full proof of Theorem 3.21."],
        "calibration_contract": {
            "ordinary_result": "ZFC proves Con(U14) iff Con(choice-free NBG) iff Con(ZF) iff Con(ZFC)",
            "basis": "definitional elimination of M; cited NBG* equivalence with documented proof repairs; definable-class expansion/reduct; constructible-universe relative consistency",
            "choice_caveat": "Con(ZF) to Con(ZFC) uses the standard L interpretation, not the presence of Choice among these fourteen sentences",
            "machine_claim": "None: no modal target emission or binary TM is supplied by this generator"},
        "axiom_count": len(rows),
        "total_formula_nodes": sum(row["formula_nodes"] for row in rows),
        "collection_proof_fixture": capture_fixture(),
        "row_metadata": [{k: v for k, v in row.items() if k != "formula"} for row in rows],
        "axioms": [row["formula"] for row in rows],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    doc = document()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"axiom_count": doc["axiom_count"],
                      "total_formula_nodes": doc["total_formula_nodes"],
                      "row_nodes": {r["source_row"]: r["formula_nodes"]
                                    for r in doc["row_metadata"]},
                      "all_sentences": all(not free(f) for f in doc["axioms"]),
                      "modal_target_emitted": False}, indent=2))


if __name__ == "__main__":
    main()
