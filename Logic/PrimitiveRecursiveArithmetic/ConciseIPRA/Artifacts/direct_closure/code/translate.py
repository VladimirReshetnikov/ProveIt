"""Untrusted proof producers for the two primitive-rule presentations.

Every output must be checked by the destination standalone checker.
"""
import json
import sys
from copy import deepcopy
from strict_q import ZERO, instantiate, lift, shift, substitute, variable, witness_instance


def map_proof(proof, images, hypotheses):
    """Simultaneous numerical substitution and context embedding of a proof."""
    rule, *args = proof
    term = lambda expression: substitute(expression, images)
    bound = lambda expression, count: substitute(expression, lift(images, count))
    same = lambda child: map_proof(child, images, hypotheses)
    branch = lambda child: map_proof(
        child, lift(images, 1),
        lambda index: 0 if index == 0 else hypotheses(index - 1) + 1,
    )
    if rule == "hyp":
        return [rule, hypotheses(args[0])]
    if rule == "zero":
        return [rule, term(args[0]), bound(args[1], 1)]
    if rule == "succ":
        return [rule, term(args[0]), term(args[1]), bound(args[2], 1)]
    if rule == "tr":
        return [rule, bound(args[0], 1), same(args[1]), same(args[2])]
    if rule == "qe":
        return [rule, term(args[0]), same(args[1]), same(args[2])]
    if rule == "de":
        return [rule, term(args[0]), same(args[1]), branch(args[2])]
    if rule == "case" or rule == "prog" and len(args) == 3:
        return [rule, bound(args[0], 2), term(args[1]), branch(args[2])]
    if rule == "prog":
        return [rule, bound(args[0], 1), branch(args[1])]
    raise ValueError("unknown rule")


def translate_proof(proof, direction):
    rule, *args = proof
    child = lambda p: translate_proof(p, direction)
    if rule in ("hyp", "zero", "succ"):
        return deepcopy(proof)
    if rule in ("tr", "qe", "de"):
        return [rule, deepcopy(args[0]), child(args[1]), child(args[2])]
    if rule == "case":
        return [rule, deepcopy(args[0]), deepcopy(args[1]), child(args[2])]
    if rule != "prog":
        raise ValueError("unknown rule")
    if direction == "old-to-q":
        matrix, witness, premise = args
        body = witness_instance(matrix, witness)
        closure_proof = ["prog", body, child(premise)]
        lifted_closure = map_proof(
            closure_proof, lambda index: variable(index + 1), lambda index: index + 1,
        )
        branch = ["qe", ["s", variable(0)], lifted_closure, ["hyp", 0]]
        return ["case", deepcopy(matrix), deepcopy(witness), branch]
    if direction == "q-to-old":
        equation, premise = args
        matrix = substitute(equation, lambda index: variable(0) if index == 0
                            else variable(index + 1))
        paired = ["prog", matrix, ZERO, child(premise)]
        return ["de", ["q", deepcopy(equation)], paired, ["hyp", 0]]
    raise ValueError("choose old-to-q or q-to-old")


def translate(document, direction):
    result = deepcopy(document)
    result["proof"] = translate_proof(document["proof"], direction)
    return result


def counts(proof):
    rule, *args = proof
    children = []
    if rule in ("tr", "qe", "de"):
        children = args[1:]
    elif rule in ("case", "prog"):
        children = [args[-1]]
    total, progress = 1, int(rule == "prog")
    for child in children:
        nodes, steps = counts(child)
        total += nodes
        progress += steps
    return total, progress


if __name__ == "__main__":
    print(json.dumps(translate(json.load(sys.stdin), sys.argv[1]), separators=(",", ":")))
