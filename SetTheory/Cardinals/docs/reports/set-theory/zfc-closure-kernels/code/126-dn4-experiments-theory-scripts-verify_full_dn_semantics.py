#!/usr/bin/env python3
"""Check the finite syntactic obligations for the full double-negation rewrite.

This is a source-level certificate, not a binary-TM runtime verifier.  Its
mathematical interpretation is explained in full_dn_proof.tex.  Python 3.10+.

Example (from the research workspace):
  python theory_work/verify_full_dn_semantics.py \
    --baseline baseline225/K225_Construction_2026-10-19/portable/results/sites225.json \
    --source theory_work/full_dn/sites_full_dn3.json \
    --recipe theory_work/full_dn/recipe3.json \
    --builder baseline225/K225_Construction_2026-10-19/portable/baseline226/vendor/proveit/build_zfc235.py \
    --dag k230-rocq/coq/prog/Dag230.v
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import cache
import hashlib
import importlib.util
import json
from pathlib import Path
import re

BASELINE_SHA256 = "86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b"
BUILDER_SHA256 = "3184f98cb7d86a6688165aa19b5e715db5fa3facf4eabd6d0ecd88d54df9a75a"
DAG_SHA256 = "7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf"
XPATHS = [
    "1110100100111010111",
    "11101001001110110101",
    "111010010011101101101",
]
BPATH = "111010010011101111011"
MACROS = {
    "and": (178, "11101001001110101110"),
    "ex": (183, "11101001001110001110"),
    "neg": (218, "111010010011100011100"),
    "im": (119, "11101001001010"),
    "all": (180, "1110100100101"),
    "ac_s1s2": (192, "11101001001110111101111"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def at(node, path):
    for bit in path:
        node = node[int(bit)]
    return node


def build(shape, atoms):
    return atoms[shape] if type(shape) is int else tuple(build(x, atoms) for x in shape)


def flatten_shape(shape):
    if type(shape) is int:
        return [shape]
    require(isinstance(shape, list) and len(shape) == 2, "Replacement shape is not a binary tree")
    return flatten_shape(shape[0]) + flatten_shape(shape[1])


def replace_paths(node, replacements, path=""):
    if path in replacements:
        return replacements[path]
    if isinstance(node[0], str):
        return node
    return tuple(replace_paths(node[i], replacements, path + str(i)) for i in (0, 1))


def read_dag(path):
    aliases = {"ENode": "N", "EInc": "CI", "EDecnz": "CD", "EBreak": "CB", "EContinue": "CC", "EHalt": "CH"}
    nodes = {}
    for line in path.read_text().splitlines():
        match = re.search(r"\| (\d+) => \((.*), (.*)\)", line)
        if match:
            def edge(text):
                words = text.split()
                return aliases[words[0]], int(words[1]) if len(words) > 1 else None
            nodes[int(match[1])] = edge(match[2]), edge(match[3])

    @cache
    def expand(edge):
        return tuple(map(expand, nodes[edge[1]])) if edge[0] == "N" else edge
    return expand


def sealed_fingerprint(builder, node):
    """A deterministic counter graph with an explicit normal-return marker.

    A maximal finite INC/JUMP segment is represented by its multiset of
    increments.  No decrement, test, or exit may occur inside such a segment.
    Thus equal fingerprints give a bisimulation up to finite, commuting
    increments, including the distinguished entry and return boundaries.
    """
    require(builder.boundary(node) == (0, 0, False), "Macro has escaping control or a halt")
    _, graph, initial = builder.graph(builder.sites((node, ("CH", None))))

    def compress(position):
        increments, visited = Counter(), set()
        while graph[position][0] in ("INC", "JUMP"):
            require(position not in visited, "Infinite deterministic increment/jump segment")
            visited.add(position)
            step = graph[position]
            if step[0] == "INC":
                increments[step[1]] += 1
                position = step[2]
            else:
                position = step[1]
        return position, tuple(sorted(increments.items()))

    queue, numbers = [], {}
    def number(position):
        if position not in numbers:
            numbers[position] = len(numbers)
            queue.append(position)
        return numbers[position]
    position, initial_increments = compress(initial)
    number(position)
    result = []
    for position in queue:
        step = graph[position]
        if step[0] == "HALT":
            result.append(("RETURN",))
        else:
            require(step[0] == "DEC", "Unexpected graph operation")
            nonzero, zero = compress(step[2]), compress(step[3])
            result.append(("DEC", step[1], (number(nonzero[0]), nonzero[1]), (number(zero[0]), zero[1])))
    return initial_increments, tuple(result)


# Symbolic code constructors.  All are uninterpreted except for their displayed
# definitions, so these checks never attempt to evaluate enormous code integers.
F = ("F",)
def I(a, b): return ("im", a, b)
def N(a): return I(a, F)
def Q(x, a): return ("all", x, a)
def M(a, b): return ("mem", a, b)
def E(a, b): return ("eq", a, b)
def A(a, b): return N(I(a, N(b)))
def X(x, a): return N(Q(x, N(a)))
def XN(x, a, b): return N(Q(x, I(a, N(b))))


def is_neg(a):
    return isinstance(a, tuple) and len(a) == 3 and a[0] == "im" and a[2] == F


def normalize(a):
    if not isinstance(a, tuple) or len(a) == 1:
        return a
    a = (a[0],) + tuple(normalize(x) for x in a[1:])
    return normalize(a[1][1]) if is_neg(a) and is_neg(a[1]) else a


def postfix(word, stack):
    stack = list(stack)
    for operation in word:
        if operation == "neg":
            stack[-1] = N(stack[-1])
        else:
            b, a = stack.pop(), stack.pop()
            stack.append({"im": I, "all": Q, "and": A, "ex": X}[operation](a, b))
    return stack


def bundles(a, b, c):
    subset = Q(c, I(M(c, a), M(c, b)))
    request = Q(b, I(c, X(b, A(c, M(b, c)))))
    request_new = Q(b, I(c, XN(b, c, M(b, c))))
    core = X(c, A(I(c, M(b, c)), Q(b, I(M(b, c), X(a, A(c, Q(a, I(subset, request))))))))
    core_new = XN(c, I(c, M(b, c)), Q(b, I(M(b, c), XN(a, c, Q(a, I(subset, request_new))))))
    vmem = I(M(a, b), Q(c, M(a, b)))
    veq = I(E(a, b), Q(c, E(a, b)))
    return A(core, A(vmem, veq)), N(I(core_new, I(vmem, N(veq))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("baseline", "source", "recipe", "builder", "dag"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.baseline.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == BASELINE_SHA256, "Wrong baseline225 source")
    require(hashlib.sha256(args.builder.read_bytes()).hexdigest() == BUILDER_SHA256, "Wrong retained source-graph builder")
    require(hashlib.sha256(args.dag.read_bytes()).hexdigest() == DAG_SHA256, "Wrong retained K230 structured source")
    spec = importlib.util.spec_from_file_location("checked_source_builder", args.builder)
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    old = builder.tree(json.loads(raw))
    candidate = builder.tree(json.loads(args.source.read_bytes()))
    recipe = json.loads(args.recipe.read_text())
    require(recipe["and_ex_paths"] == XPATHS and recipe["and_and_acdup_paths"] == [BPATH], "Wrong replacement paths")
    require(flatten_shape(recipe["shape_x"]) == list(range(4)), "Existential/conjunction shape changes its macro word")
    require(flatten_shape(recipe["shape_b"]) == list(range(5)), "Bundle-ending shape changes its macro word")
    macros = {name: at(old, path) for name, (_, path) in MACROS.items()}
    expand = read_dag(args.dag)
    macro_checks = []
    for name, (index, path) in MACROS.items():
        left = sealed_fingerprint(builder, macros[name])
        right = sealed_fingerprint(builder, expand(("N", index)))
        require(left == right, f"The {name} macro is not the documented K230 macro")
        macro_checks.append({"name": name, "dag230_node": index, "source_path": path, "guard_nodes": len(left[1])})
    for path in XPATHS:
        require(at(old, path) == (macros["and"], macros["ex"]), "Wrong old and/ex subtree")
    require(at(old, BPATH) == (macros["and"], (macros["and"], macros["ac_s1s2"])), "Wrong old bundle-ending subtree")
    xnew = build(recipe["shape_x"], [macros[n] for n in ("neg", "im", "all", "neg")])
    bnew = build(recipe["shape_b"], [macros[n] for n in ("neg", "im", "im", "neg", "ac_s1s2")])
    expected = replace_paths(old, {**{path: xnew for path in XPATHS}, BPATH: bnew})
    reference_word, reference_graph, reference_initial = builder.graph(builder.sites(expected))
    candidate_word, candidate_graph, candidate_initial = builder.graph(builder.sites(candidate))
    require([x[1:] for x in candidate_word] == [x[1:] for x in reference_word], "Candidate changes the instruction word")
    require((candidate_graph, candidate_initial) == (reference_graph, reference_initial), "Candidate changes a source guard successor")

    tail, x, a, b, p = ((s,) for s in ("tail", "x", "A", "B", "P"))
    old_x = postfix(["and", "ex"], [tail, x, a, b])
    new_x = postfix(["neg", "im", "all", "neg"], [tail, x, a, b])
    require(old_x == [tail, X(x, A(a, b))], "Old existential/conjunction stack contract")
    require(new_x == [tail, XN(x, a, b)], "New existential/conjunction stack contract")
    require(normalize(old_x[-1]) == normalize(new_x[-1]), "Existential/conjunction double negation")
    old_b = postfix(["and", "and"], [tail, p, a, b])
    new_b = postfix(["neg", "im", "im", "neg"], [tail, p, a, b])
    require(old_b == [tail, A(p, A(a, b))], "Old triple-conjunction stack contract")
    require(new_b == [tail, N(I(p, I(a, N(b))))], "New triple-conjunction stack contract")
    require(normalize(old_b[-1]) == normalize(new_b[-1]), "Triple-conjunction double negation")
    old_formula, new_formula = bundles(("a",), ("b",), ("c",))
    require(normalize(old_formula) == normalize(new_formula), "Complete old/new bundles do not normalize identically")
    result = {
        "status": "PASS_FULL_DN_SOURCE_AND_SYMBOLIC_FORMULA",
        "baseline_sha256": BASELINE_SHA256,
        "source_sha256": hashlib.sha256(args.source.read_bytes()).hexdigest(),
        "builder_sha256": BUILDER_SHA256,
        "dag230_sha256": DAG_SHA256,
        "recipe_sha256": hashlib.sha256(args.recipe.read_bytes()).hexdigest(),
        "source_metrics": builder.metrics(candidate),
        "macro_checks": macro_checks,
        "replacement_paths": XPATHS + [BPATH],
        "stack_contracts": "Both rewrites consume exactly two stack operands and preserve every lower stack entry; scratch registers return to zero.",
        "formula_check": "Identical constructor expressions after recursive double-negation elimination; quantifier labels and freshness tests are unchanged.",
        "scope": "Finite source and formula checks; the universal logical argument is full_dn_proof.tex, and binary runtime requires its separate certificate.",
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
