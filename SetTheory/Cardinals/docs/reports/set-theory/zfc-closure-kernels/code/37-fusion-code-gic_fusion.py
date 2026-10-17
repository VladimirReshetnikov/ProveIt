#!/usr/bin/env python3
"""Single-instance GIC refutation interface, sharing EPSC fusion syntax.

No CP or irreflexivity premise is needed for the fusion equivalence.
The implementation is an ordinary finite reference, not a machine compiler.
"""

from __future__ import annotations

from dataclasses import replace
from itertools import product
import argparse
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run this reference with assertions enabled; Python -O and -OO are not supported.")

from epsc_fusion import (
    BOTTOM, Formula, Fusion, Structure, all_, and_, eval_formula,
    ex, free, fresh_start, fuse, imp, ite, mem, node_count, structures,
)


def gic(matrix: Formula) -> Formula:
    """Universally closed global-image collection, exactly as in ProveIt."""
    x, y = 0, 1
    a, b = range(fresh_start([matrix]), fresh_start([matrix]) + 2)
    coverage = all_(x, imp(mem(x, a),
                           imp(ex(y, matrix), ex(y, and_(mem(y, b), matrix)))))
    support = all_(y, imp(mem(y, b), ex(x, matrix)))
    result = all_(a, ex(b, and_(coverage, support)))
    for parameter in sorted(free(matrix) - {x, y}, reverse=True):
        result = all_(parameter, result)
    assert not free(result)
    return result


def fuse_gic(matrices: list[Formula]) -> Fusion:
    """Use atomic selectors and replace the two bootstrap leaves by Bottom."""
    skeleton = fuse(matrices, "atomic")

    def build(leaves: tuple[int, ...], depth: int) -> Formula:
        if len(leaves) == 1:
            return BOTTOM if leaves[0] == -1 else matrices[leaves[0]]
        mid = len(leaves) // 2
        return ite(skeleton.guards[depth], build(leaves[mid:], depth + 1),
                   build(leaves[:mid], depth + 1))

    return replace(skeleton, matrix=build(skeleton.leaves, 0),
                   base=BOTTOM, mode="gic_atomic")


def gic_relation(model: Structure, relation: int) -> bool:
    size = model.size
    d = range(size)

    def r(x: int, y: int) -> bool:
        return bool((relation >> (size*x+y)) & 1)

    return all(any(
        all(not (model.member(x, a) and any(r(x, y) for y in d))
            or any(model.member(y, b) and r(x, y) for y in d) for x in d)
        and all(not model.member(y, b) or any(r(x, y) for x in d) for y in d)
        for b in d) for a in d)


def gic_at(matrix: Formula, model: Structure, params: dict[int, int]) -> bool:
    relation = sum(int(eval_formula(matrix, model, {**params, 0:x, 1:y}))
                   << (model.size*x+y)
                   for x in range(model.size) for y in range(model.size))
    return gic_relation(model, relation)


def gic_holds(matrix: Formula, model: Structure) -> bool:
    parameters = sorted(free(matrix) - {0, 1})
    return all(gic_at(matrix, model, dict(zip(parameters, values)))
               for values in product(range(model.size), repeat=len(parameters)))


def run_tests() -> dict:
    counts = {"bottom_bootstrap_structures": 0, "arbitrary_relation_fusions": 0,
              "syntactic_closed_fusions": 0, "expanded_wrapper_comparisons": 0,
              "exact_size_checks": 0, "no_edge_controls": 0}
    for size in (1, 2, 3):
        for model in structures(size):
            assert gic_holds(BOTTOM, model) == any(model.is_empty(e) for e in range(size))
            counts["bottom_bootstrap_structures"] += 1

    for model in structures(2):
        valid = [gic_relation(model, r) for r in range(16)]
        for n in (1, 2, 3):
            skeleton = fuse_gic([BOTTOM]*n)
            for bundle in product(range(16), repeat=n):
                left = True
                for h in range(2):
                    for assignment in product(range(2), repeat=len(skeleton.selectors)):
                        code = 0
                        for s in assignment:
                            code = 2*code + int(model.member(h, s))
                        index = skeleton.branches[code]
                        relation = 0 if index == -1 else bundle[index]
                        left = left and valid[relation]
                right = valid[0] and all(valid[r] for r in bundle)
                assert left == right
                counts["arbitrary_relation_fusions"] += 1

    samples = [BOTTOM, imp(BOTTOM, BOTTOM), mem(0,1), mem(1,0), mem(0,2),
               imp(mem(0,2),mem(2,1)), all_(0,mem(0,1))]
    batches = [[a] for a in samples] + [[a,b] for a in samples for b in samples]
    batches += [[], samples[:3], samples[:4], samples]
    for size in (1,2):
        for model in structures(size):
            for batch in batches:
                f = fuse_gic(batch)
                assert gic_holds(f.matrix,model) == (
                    gic_holds(BOTTOM,model) and all(gic_holds(a,model) for a in batch))
                counts["syntactic_closed_fusions"] += 1
            for a in samples + [fuse_gic(samples[:2]).matrix]:
                assert eval_formula(gic(a),model,{}) == gic_holds(a,model)
                counts["expanded_wrapper_comparisons"] += 1

    for n in range(10):
        matrices = [samples[i%len(samples)] for i in range(n)]
        f = fuse_gic(matrices)
        expected = sum(node_count(a) for a in matrices) + (11*n+13 if n else 1)
        assert node_count(f.matrix) == expected
        counts["exact_size_checks"] += 1

    # Without any membership edges, no true atomic selector exists.
    # Nevertheless every GIC instance is true: all input domains and all
    # output supports are empty. This is the missing case in a naive proof.
    no_edge = Structure(2,(0,0))
    assert all(gic_relation(no_edge,r) for r in range(16))
    counts["no_edge_controls"] += 1
    return {"status":"PASS", "tests":counts,
            "scope":"Finite syntax/semantics reference; pure-FOL proof is in the manuscript. No CP hypothesis, TM compilation, or consistency test."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--example",type=Path)
    args = parser.parse_args()
    result = run_tests()
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    if args.example:
        f = fuse_gic([mem(0,2),imp(mem(0,2),mem(2,1)),all_(4,mem(4,0))])
        data = {"matrix":f.matrix,"closed_gic_axiom":gic(f.matrix),
                "selectors":f.selectors,"anchor":f.anchor,"leaves":f.leaves,
                "branches":f.branches,"matrix_tree_nodes":node_count(f.matrix),
                "closed_axiom_tree_nodes":node_count(gic(f.matrix))}
        args.example.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
