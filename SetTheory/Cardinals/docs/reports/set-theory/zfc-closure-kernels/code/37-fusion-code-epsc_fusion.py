#!/usr/bin/env python3
"""Equality-free finite fusion of EPSC instances.

This is an executable reference for the manuscript's syntactic construction,
not a Turing-machine compiler or a proof-assistant-certified program.
Only Python's standard library is needed.  Every public formula uses the
ordinary named-variable basis Bottom, membership, implication and forall.
Designated free matrix variables are x=0 and y=1; all other free variables
are universally closed parameters of the EPSC instance.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import argparse
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run this reference with assertions enabled; Python -O and -OO are not supported.")

Formula = tuple
BOTTOM: Formula = ("bot",)


def mem(x: int, y: int) -> Formula:
    return ("mem", x, y)


def imp(a: Formula, b: Formula) -> Formula:
    return ("imp", a, b)


def all_(x: int, a: Formula) -> Formula:
    return ("all", x, a)


def neg(a: Formula) -> Formula:
    return imp(a, BOTTOM)


def and_(a: Formula, b: Formula) -> Formula:
    return neg(imp(a, neg(b)))


def or_(a: Formula, b: Formula) -> Formula:
    return imp(neg(a), b)


def ex(x: int, a: Formula) -> Formula:
    return neg(all_(x, neg(a)))


def ite(g: Formula, yes: Formula, no: Formula) -> Formula:
    # Each branch occurs exactly once in the formula tree.
    return and_(imp(g, yes), imp(neg(g), no))


def names(a: Formula) -> set[int]:
    tag = a[0]
    if tag == "bot":
        return set()
    if tag == "mem":
        return {a[1], a[2]}
    if tag == "imp":
        return names(a[1]) | names(a[2])
    if tag == "all":
        return {a[1]} | names(a[2])
    raise ValueError(f"unknown formula tag: {tag!r}")


def free(a: Formula) -> set[int]:
    tag = a[0]
    if tag == "bot":
        return set()
    if tag == "mem":
        return {a[1], a[2]}
    if tag == "imp":
        return free(a[1]) | free(a[2])
    if tag == "all":
        return free(a[2]) - {a[1]}
    raise ValueError(f"unknown formula tag: {tag!r}")


def node_count(a: Formula) -> int:
    if a[0] in ("bot", "mem"):
        return 1
    if a[0] == "imp":
        return 1 + node_count(a[1]) + node_count(a[2])
    if a[0] == "all":
        return 1 + node_count(a[2])
    raise ValueError(a)


def fresh_start(formulas: list[Formula]) -> int:
    used = {0, 1}
    for a in formulas:
        used |= names(a)
    return max(used) + 1


def empty(x: int, bound: int) -> Formula:
    assert x != bound
    return all_(bound, neg(mem(bound, x)))


def subset(x: int, y: int, bound: int) -> Formula:
    assert bound not in (x, y)
    return all_(bound, imp(mem(bound, x), mem(bound, y)))


def good_selector(s: int, z: int, w: int) -> Formula:
    """G(s) = E(s) -> forall z E(z), with fresh distinct bound names."""
    assert len({s, z, w}) == 3
    return imp(empty(s, w), all_(z, empty(z, w)))


def epsc(matrix: Formula) -> Formula:
    """The actual universally closed EPSC wrapper in the primitive basis."""
    x, y = 0, 1
    b, c, z = range(fresh_start([matrix]), fresh_start([matrix]) + 3)
    bounded = all_(x, ex(b, all_(y, imp(matrix, subset(y, b, z)))))
    active = or_(empty(x, z), mem(x, c))
    closure = all_(x, all_(y, imp(and_(active, matrix), mem(y, c))))
    support = all_(y, imp(mem(y, c), ex(x, matrix)))
    result = imp(bounded, ex(c, and_(closure, support)))
    for parameter in sorted(free(matrix) - {x, y}, reverse=True):
        result = all_(parameter, result)
    assert not free(result)
    return result


@dataclass(frozen=True)
class Fusion:
    matrix: Formula
    base: Formula
    selectors: tuple[int, ...]
    guards: tuple[Formula, ...]
    branches: tuple[int, ...]  # -1 is the base E(y); otherwise an input index.
    original_parameters: tuple[int, ...]
    mode: str
    anchor: int | None
    leaves: tuple[int, ...]

    def json_data(self) -> dict:
        return {
            "formula_basis": ["bot", "mem", "imp", "all"],
            "designated_matrix_variables": {"x": 0, "y": 1},
            "matrix": self.matrix,
            "base_matrix": self.base,
            "selectors": self.selectors,
            "guards": self.guards,
            "branch_indices": self.branches,
            "tree_leaf_indices": self.leaves,
            "selector_mode": self.mode,
            "shared_atomic_anchor": self.anchor,
            "original_parameters": self.original_parameters,
            "fused_matrix_tree_nodes": node_count(self.matrix),
            "closed_axiom_tree_nodes": node_count(epsc(self.matrix)),
            "closed_axiom": epsc(self.matrix),
        }


def fuse(matrices: list[Formula], mode: str = "g") -> Fusion:
    """Construct A_fused iff the conjunction of A_E(y), A_1, ..., A_n.

    mode="g" uses one bootstrap leaf and logically inhabited G selectors;
    modes "empty" and "atomic" reserve both extreme leaves for bootstrap.
    The tree is balanced over exactly n+1 (or n+2) leaves, without padding.
    Empty input returns the base without selectors in every mode.
    Fresh names avoid every free and bound input name.
    """
    n = len(matrices)
    if mode not in ("g", "empty", "atomic"):
        raise ValueError("mode must be g, empty, or atomic")
    if n == 0:
        leaves = (-1,)
    elif mode == "g":
        leaves = tuple(range(n)) + (-1,)
    else:
        leaves = (-1,) + tuple(range(n)) + (-1,)
    k = (len(leaves) - 1).bit_length()
    first = fresh_start(matrices)
    anchor = first if mode == "atomic" and n else None
    first_selector = first + int(anchor is not None)
    selectors = tuple(range(first_selector, first_selector + k))
    z, w = first_selector + k, first_selector + k + 1
    base = empty(1, w)
    if mode == "g":
        guards = tuple(good_selector(s, z, w) for s in selectors)
    elif mode == "empty":
        guards = tuple(empty(s, w) for s in selectors)
    else:
        guards = tuple(mem(anchor, s) for s in selectors)

    def build(indices: tuple[int, ...], depth: int) -> Formula:
        if len(indices) == 1:
            index = indices[0]
            return base if index == -1 else matrices[index]
        mid = len(indices) // 2
        return ite(guards[depth], build(indices[mid:], depth + 1),
                   build(indices[:mid], depth + 1))

    def branch(indices: tuple[int, ...], code: int, depth: int) -> int:
        if len(indices) == 1:
            return indices[0]
        mid = len(indices) // 2
        bit = (code >> (k - depth - 1)) & 1
        return branch(indices[mid:] if bit else indices[:mid], code, depth + 1)

    branches = tuple(branch(leaves, code, 0) for code in range(1 << k))
    original_parameters = set()
    for a in matrices:
        original_parameters |= free(a) - {0, 1}
    result = build(leaves, 0)
    new_params = set(selectors) | (set() if anchor is None else {anchor})
    assert free(result) <= ({0, 1} | original_parameters | new_params)
    assert branches[-1] == -1
    if mode != "g":
        assert branches[0] == -1
    return Fusion(result, base, selectors, guards, branches,
                  tuple(sorted(original_parameters)), mode, anchor, leaves)


@dataclass(frozen=True)
class Structure:
    size: int
    # Row i has bit j precisely when i belongs to j.
    rows: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.size <= 0 or len(self.rows) != self.size:
            raise ValueError("the first-order domain must be finite and nonempty")
        if any(not 0 <= row < (1 << self.size) for row in self.rows):
            raise ValueError("invalid finite relation")

    def member(self, i: int, j: int) -> bool:
        return bool((self.rows[i] >> j) & 1)

    def is_empty(self, j: int) -> bool:
        return all(not self.member(i, j) for i in range(self.size))

    def is_subset(self, i: int, j: int) -> bool:
        return all(not self.member(t, i) or self.member(t, j)
                   for t in range(self.size))


def eval_formula(a: Formula, model: Structure, values: dict[int, int]) -> bool:
    tag = a[0]
    if tag == "bot":
        return False
    if tag == "mem":
        return model.member(values[a[1]], values[a[2]])
    if tag == "imp":
        return not eval_formula(a[1], model, values) or eval_formula(a[2], model, values)
    if tag == "all":
        return all(eval_formula(a[2], model, {**values, a[1]: v})
                   for v in range(model.size))
    raise ValueError(a)


def epsc_at(matrix: Formula, model: Structure, params: dict[int, int]) -> bool:
    """Independent direct semantics, avoiding the generated wrapper AST."""
    d = range(model.size)
    r = [[eval_formula(matrix, model, {**params, 0: x, 1: y})
          for y in d] for x in d]
    bounded = all(any(all(not r[x][y] or model.is_subset(y, b) for y in d)
                      for b in d) for x in d)
    if not bounded:
        return True
    for c in d:
        closure = all(not ((model.is_empty(x) or model.member(x, c)) and r[x][y])
                      or model.member(y, c) for x in d for y in d)
        support = all(not model.member(y, c) or any(r[x][y] for x in d)
                      for y in d)
        if closure and support:
            return True
    return False


def epsc_holds(matrix: Formula, model: Structure) -> bool:
    params = sorted(free(matrix) - {0, 1})
    return all(epsc_at(matrix, model, dict(zip(params, values)))
               for values in product(range(model.size), repeat=len(params)))


def structures(size: int):
    for bits in range(1 << (size * size)):
        yield Structure(size, tuple((bits >> (i * size)) & ((1 << size) - 1)
                                    for i in range(size)))


def run_tests() -> dict:
    counts = {"selector_existence_structures": 0,
              "base_axiom_structures": 0,
              "full_fusion_equivalences": 0,
              "arbitrary_relation_fusion_equivalences": 0,
              "wrapper_semantics_checks": 0,
              "branch_evaluations": 0,
              "exact_size_checks": 0,
              "adversarial_controls": 0}
    guard = good_selector(5, 6, 7)
    epsilon = empty(1, 8)
    for size in (1, 2, 3):
        for model in structures(size):
            selector_values = [eval_formula(guard, model, {5: s}) for s in range(size)]
            assert any(selector_values)
            counts["selector_existence_structures"] += 1
            base_valid = epsc_holds(epsilon, model)
            exact_empty_class = any(all(model.member(y, c) == model.is_empty(y)
                                       for y in range(size)) for c in range(size))
            assert base_valid == exact_empty_class
            if base_valid:
                assert any(model.is_empty(s) for s in range(size))
                assert any(not model.is_empty(s) for s in range(size))
                assert set(selector_values) == {False, True}
            counts["base_axiom_structures"] += 1

    samples = [BOTTOM, imp(BOTTOM, BOTTOM), mem(0, 1), mem(1, 0),
               neg(mem(0, 0)), empty(1, 3), mem(0, 2), mem(2, 1),
               imp(mem(0, 2), mem(2, 1)), all_(4, imp(mem(4, 0), mem(4, 1))),
               all_(0, imp(mem(0, 2), mem(0, 1)))]
    batches = ([a] for a in samples)
    batches = list(batches) + [[a, b] for a in samples for b in samples]
    batches += [samples[i:i + 3] for i in range(len(samples) - 2)]
    batches += [[], samples[:7], samples[:8]]
    for size in (1, 2):
        for model in structures(size):
            for batch in batches:
                for mode in ("g", "empty", "atomic"):
                    fused = fuse(batch, mode)
                    left = epsc_holds(fused.matrix, model)
                    right = epsc_holds(fused.base, model) and all(epsc_holds(a, model) for a in batch)
                    assert left == right, (model, batch, mode)
                    counts["full_fusion_equivalences"] += 1
            for a in samples[:6] + [fuse(samples[:2], mode).matrix for mode in ("g", "empty", "atomic")]:
                assert eval_formula(epsc(a), model, {}) == epsc_holds(a, model)
                counts["wrapper_semantics_checks"] += 1

    # A concrete model of B: 0 is empty and 1 is exactly {0}.
    model = Structure(2, (2, 0))
    assert epsc_holds(epsilon, model)
    for n in range(10):
        batch = [samples[i % len(samples)] for i in range(n)]
        for mode in ("g", "empty", "atomic"):
            fused = fuse(batch, mode)
            expected = sum(node_count(a) for a in batch)
            expected += 4 if not n else {"g": 29*n+4, "empty": 17*n+25, "atomic": 11*n+19}[mode]
            assert node_count(fused.matrix) == expected
            assert node_count(epsc(fused.matrix)) == 3*expected + 48 + len(free(fused.matrix)-{0,1})
            counts["exact_size_checks"] += 1
            for pattern in product((0, 1), repeat=len(fused.selectors)):
                # G(0)=false, G(1)=true; E reverses them; with h=0,
                # R(h,0)=false and R(h,1)=true.
                chosen = tuple(1-bit if mode == "empty" else bit for bit in pattern)
                values = dict(zip(fused.selectors, chosen))
                if fused.anchor is not None:
                    values[fused.anchor] = 0
                index = 0
                for bit in pattern:
                    index = 2 * index + bit
                branch = fused.branches[index]
                selected = fused.base if branch == -1 else batch[branch]
                for params in product(range(2), repeat=len(fused.original_parameters)):
                    valuation = {**values, **dict(zip(fused.original_parameters, params))}
                    for x, y in product(range(2), repeat=2):
                        valuation = {**valuation, 0: x, 1: y}
                        assert eval_formula(fused.matrix, model, valuation) == eval_formula(selected, model, valuation)
                        counts["branch_evaluations"] += 1

    # Independently enumerate every 2- and 3-matrix bundle of arbitrary
    # binary relations over every two-point membership structure.  Here
    # the matrices are arbitrary relations, not just the syntactic samples.
    def relation_axiom(model: Structure, relation: int) -> bool:
        def r(x: int, y: int) -> bool:
            return bool((relation >> (2 * x + y)) & 1)
        bounded = all(any(all(not r(x, y) or model.is_subset(y, b)
                              for y in range(2)) for b in range(2))
                      for x in range(2))
        if not bounded:
            return True
        return any(
            all(not ((model.is_empty(x) or model.member(x, c)) and r(x, y))
                or model.member(y, c) for x in range(2) for y in range(2))
            and all(not model.member(y, c) or any(r(x, y) for x in range(2))
                    for y in range(2))
            for c in range(2))

    for model in structures(2):
        all_empty = all(model.is_empty(v) for v in range(2))
        g = [not model.is_empty(s) or all_empty for s in range(2)]
        e_relation = sum(int(model.is_empty(y)) << (2 * x + y)
                         for x in range(2) for y in range(2))
        validity = [relation_axiom(model, r) for r in range(16)]
        for n in (2, 3):
            for mode in ("g", "empty", "atomic"):
                skeleton = fuse([BOTTOM]*n, mode)
                k = len(skeleton.selectors)
                for bundle in product(range(16), repeat=n):
                    fused_valid = True
                    for h in (range(2) if mode == "atomic" else (0,)):
                        for assignment in product(range(2), repeat=k):
                            code = 0
                            for s in assignment:
                                value = g[s] if mode == "g" else model.is_empty(s) if mode == "empty" else model.member(h, s)
                                code = 2 * code + int(value)
                            selected = skeleton.branches[code]
                            r = e_relation if selected == -1 else bundle[selected]
                            fused_valid = fused_valid and validity[r]
                    target = validity[e_relation] and all(validity[r] for r in bundle)
                    assert fused_valid == target
                    counts["arbitrary_relation_fusion_equivalences"] += 1

    # Replacing G(s) by E(s) destroys bootstrap: in the full one-point
    # graph every selector is false, so the true-matrix branch evades B.
    full_one = Structure(1, (1,))
    naive = ite(empty(5, 6), epsilon, imp(BOTTOM, BOTTOM))
    assert epsc_holds(naive, full_one) and not epsc_holds(epsilon, full_one)
    counts["adversarial_controls"] += 1
    # Omitting B entirely also destroys the equivalence on the empty graph.
    empty_one = Structure(1, (0,))
    assert epsc_holds(BOTTOM, empty_one) and not epsc_holds(epsilon, empty_one)
    counts["adversarial_controls"] += 1

    return {"status": "PASS", "tests": counts,
            "scope": "Finite tests of a reference construction; not an unbounded proof, TM compilation, or consistency test."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write finite regression evidence as JSON")
    parser.add_argument("--example", type=Path, help="write one exact fused formula and closed EPSC axiom")
    args = parser.parse_args()
    result = run_tests()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    if args.example:
        matrices = [mem(0, 2), imp(mem(0, 2), mem(2, 1)), all_(4, mem(4, 0))]
        examples = {mode: fuse(matrices, mode).json_data() for mode in ("g", "empty", "atomic")}
        args.example.write_text(json.dumps(examples, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
