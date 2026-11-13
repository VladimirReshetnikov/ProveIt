"""Readable reference checker for the selectively normalized six-rule calculus.

This is a reference implementation, not a claim of a new checker-size record.
The command line checks a closed theorem certificate with exactly two fields:
{"goal": FORMULA, "proof": PROOF}. See README.txt for syntax and rule records.
"""
from __future__ import annotations

import json
import sys


class CheckError(Exception):
    """Malformed syntax or a derivation that does not justify its target."""


def name(value):
    if not isinstance(value, str) or not value:
        raise CheckError("A variable name must be a nonempty string")
    return value


def zero(value):
    return type(value) is int and value == 0


def successor(value):
    return isinstance(value, list) and len(value) == 2 and value[0] == "S"


def numeral(value):
    result = 0
    while successor(value):
        result += 1
        value = value[1]
    return result if zero(value) else None


def validate_term(term, scope):
    if zero(term):
        return
    if isinstance(term, str):
        if term not in scope:
            raise CheckError(f"Unbound numerical variable: {term}")
        return
    if not isinstance(term, list) or not term:
        raise CheckError("Malformed term")
    if term[0] == "S" and len(term) == 2:
        validate_term(term[1], scope)
        return
    if term[0] == "I" and len(term) == 5:
        _, counter, seed, state, body = term
        name(state)
        validate_term(counter, scope)
        validate_term(seed, scope)
        validate_term(body, scope | {state})
        return
    raise CheckError("Unknown term constructor or wrong arity")


def validate_formula(formula, scope):
    if not isinstance(formula, list) or not formula:
        raise CheckError("Malformed formula")
    tag = formula[0]
    if tag == "=" and len(formula) == 3:
        validate_term(formula[1], scope)
        validate_term(formula[2], scope)
        return
    if tag == "Q" and len(formula) == 3:
        variable = name(formula[1])
        validate_formula(formula[2], scope | {variable})
        return
    if tag == "D" and len(formula) == 4:
        witness = name(formula[1])
        index = name(formula[2])
        if witness == index:
            raise CheckError("D must bind two distinct variable names")
        validate_formula(formula[3], scope | {witness, index})
        return
    raise CheckError("Unknown formula constructor or wrong arity")


def free_term(term):
    if zero(term):
        return set()
    if isinstance(term, str):
        return {term}
    if term[0] == "S":
        return free_term(term[1])
    _, counter, seed, state, body = term
    return free_term(counter) | free_term(seed) | (free_term(body) - {state})


def free_formula(formula):
    if formula[0] == "=":
        return free_term(formula[1]) | free_term(formula[2])
    if formula[0] == "Q":
        return free_formula(formula[2]) - {formula[1]}
    return free_formula(formula[3]) - {formula[1], formula[2]}


def all_names(tree):
    """All strings are harmless over-approximations, including constructor tags."""
    if isinstance(tree, str):
        return {tree}
    if isinstance(tree, list):
        result = set()
        for child in tree:
            result |= all_names(child)
        return result
    return set()


def fresh(avoid):
    index = 0
    while f"_s{index}" in avoid:
        index += 1
    return f"_s{index}"


def replacement_names(replacements):
    result = set(replacements)
    for term in replacements.values():
        result |= all_names(term)
    return result


def replacement_free(replacements):
    result = set()
    for term in replacements.values():
        result |= free_term(term)
    return result


def substitute_term(term, replacements):
    """Simultaneous, capture-avoiding substitution for free numerical variables."""
    if zero(term):
        return 0
    if isinstance(term, str):
        return replacements.get(term, term)
    if term[0] == "S":
        return ["S", substitute_term(term[1], replacements)]
    _, counter, seed, state, body = term
    new_counter = substitute_term(counter, replacements)
    new_seed = substitute_term(seed, replacements)
    active = {key: value for key, value in replacements.items() if key != state}
    if state in replacement_free(active):
        new_state = fresh(all_names(term) | replacement_names(active))
        body = substitute_term(body, {state: new_state})
        state = new_state
    return ["I", new_counter, new_seed, state, substitute_term(body, active)]


def substitute_formula(formula, replacements):
    if formula[0] == "=":
        return ["=", substitute_term(formula[1], replacements),
                substitute_term(formula[2], replacements)]
    if formula[0] == "Q":
        tag, bound, body = formula
        active = {key: value for key, value in replacements.items() if key != bound}
        if bound in replacement_free(active):
            renamed = fresh(all_names(formula) | replacement_names(active))
            body = substitute_formula(body, {bound: renamed})
            bound = renamed
        return [tag, bound, substitute_formula(body, active)]
    tag, witness, index, body = formula
    active = {
        key: value for key, value in replacements.items()
        if key not in {witness, index}
    }
    avoid = all_names(formula) | replacement_names(active)
    image_variables = replacement_free(active)
    if witness in image_variables:
        renamed = fresh(avoid)
        avoid.add(renamed)
        body = substitute_formula(body, {witness: renamed})
        witness = renamed
    if index in image_variables:
        renamed = fresh(avoid)
        body = substitute_formula(body, {index: renamed})
        index = renamed
    return [tag, witness, index, substitute_formula(body, active)]


def term_key(term, bound=()):
    """An alpha-invariant representation; nearest binder has index zero."""
    if zero(term):
        return ("zero",)
    if isinstance(term, str):
        if term in bound:
            return ("bound", bound[::-1].index(term))
        return ("free", term)
    if term[0] == "S":
        return ("S", term_key(term[1], bound))
    _, counter, seed, state, body = term
    return ("I", term_key(counter, bound), term_key(seed, bound),
            term_key(body, bound + (state,)))


def formula_key(formula, bound=()):
    if formula[0] == "=":
        return ("=", term_key(formula[1], bound), term_key(formula[2], bound))
    if formula[0] == "Q":
        return ("Q", formula_key(formula[2], bound + (formula[1],)))
    return ("D", formula_key(formula[3], bound + (formula[1], formula[2])))


def normalize_term(term, environment=None, statistics=None):
    """N2 by an environment evaluator on strict subterms of the original tree.

    Environment values are already normalized. An iterator activation makes
    at most four recursive calls: counter, seed, and its original body at
    most twice. Recursive calls never receive a constructed substituted tree.
    Binder names may change; fixed-point claims are modulo alpha-equivalence.
    """
    environment = {} if environment is None else environment
    if statistics is not None:
        statistics["calls"] = statistics.get("calls", 0) + 1
    if zero(term):
        return 0
    if isinstance(term, str):
        return environment.get(term, term)
    if term[0] == "S":
        return ["S", normalize_term(term[1], environment, statistics)]
    _, raw_counter, raw_seed, state, raw_body = term
    counter = normalize_term(raw_counter, environment, statistics)
    seed = normalize_term(raw_seed, environment, statistics)
    count = numeral(counter)
    if count == 0:
        return seed
    if count in (1, 2):
        value = seed
        for _ in range(count):
            value = normalize_term(raw_body, environment | {state: value}, statistics)
        return value
    renamed = fresh(all_names(term) | replacement_names(environment))
    body = normalize_term(raw_body, environment | {state: renamed}, statistics)
    if successor(counter) and renamed not in free_term(body):
        return body
    return ["I", counter, seed, renamed, body]


def normalize_formula(formula):
    if formula[0] == "=":
        return ["=", normalize_term(formula[1]), normalize_term(formula[2])]
    if formula[0] == "Q":
        return ["Q", formula[1], normalize_formula(formula[2])]
    return ["D", formula[1], formula[2], normalize_formula(formula[3])]


def equal_formulas(left, right):
    return formula_key(normalize_formula(left)) == formula_key(normalize_formula(right))


def fields(proof, required):
    if not isinstance(proof, dict) or set(proof) != {"rule", *required}:
        raise CheckError("Wrong fields in a proof record")


def require_goal(goal, expected):
    if not equal_formulas(goal, expected):
        raise CheckError("Rule conclusion does not match its target")


def check_proof(goal, proof, context=(), scope=frozenset()):
    """Check a sequent; only check_certificate exposes the closed-theorem API."""
    scope = set(scope)
    validate_formula(goal, scope)
    for assumption in context:
        validate_formula(assumption, scope)
    if not isinstance(proof, dict) or "rule" not in proof:
        raise CheckError("A proof must be a rule record")
    rule = proof["rule"]
    if rule == "hyp":
        fields(proof, ())
        if not any(equal_formulas(goal, assumption) for assumption in context):
            raise CheckError("The target is not an assumption")
        return
    if rule == "succ":
        fields(proof, ("n", "a", "u", "h"))
        counter, seed, state, body = (proof[key] for key in ("n", "a", "u", "h"))
        name(state)
        validate_term(counter, scope)
        validate_term(seed, scope)
        validate_term(body, scope | {state})
        previous = ["I", counter, seed, state, body]
        expected = ["=", ["I", ["S", counter], seed, state, body],
                    substitute_term(body, {state: previous})]
        require_goal(goal, expected)
        return
    if rule == "vsub":
        fields(proof, ("x", "t", "u", "v", "major", "minor"))
        variable = name(proof["x"])
        if variable not in scope:
            raise CheckError("VSub source must be an available numerical variable")
        image, left, right = (proof[key] for key in ("t", "u", "v"))
        for term in (image, left, right):
            validate_term(term, scope)
        require_goal(goal, ["=", right, substitute_term(left, {variable: image})])
        check_proof(["=", variable, image], proof["major"], context, scope)
        check_proof(["=", left, right], proof["minor"], context, scope)
        return
    if rule == "qe":
        fields(proof, ("y", "body", "t", "major", "base"))
        index, body, image = name(proof["y"]), proof["body"], proof["t"]
        validate_formula(["Q", index, body], scope)
        validate_term(image, scope)
        require_goal(goal, substitute_formula(body, {index: image}))
        check_proof(["Q", index, body], proof["major"], context, scope)
        check_proof(substitute_formula(body, {index: 0}), proof["base"], context, scope)
        return
    if rule == "de":
        fields(proof, ("x", "y", "body", "b", "major", "minor"))
        witness, index = name(proof["x"]), name(proof["y"])
        body, eigenvariable = proof["body"], name(proof["b"])
        major = ["D", witness, index, body]
        validate_formula(major, scope)
        if eigenvariable in scope:
            raise CheckError("DE eigenvariable is not fresh")
        check_proof(major, proof["major"], context, scope)
        opened = substitute_formula(["Q", index, body], {witness: eigenvariable})
        check_proof(goal, proof["minor"], context + (opened,), scope | {eigenvariable})
        return
    if rule == "wi":
        fields(proof, ("x", "y", "body", "t", "z", "step"))
        witness, index = name(proof["x"]), name(proof["y"])
        body, image, eigenvariable = proof["body"], proof["t"], name(proof["z"])
        target = ["D", witness, index, body]
        validate_formula(target, scope)
        validate_term(image, scope)
        if eigenvariable in scope:
            raise CheckError("WI eigenvariable is not fresh")
        require_goal(goal, target)
        # Deliberately inspect the raw hint. N(image)=0 does not select progress.
        start = eigenvariable if body[0] == "=" and zero(image) else 0
        base = substitute_formula(body, {witness: image, index: start})
        step = substitute_formula(body, {witness: image, index: ["S", eigenvariable]})
        check_proof(step, proof["step"], context + (base,), scope | {eigenvariable})
        return
    raise CheckError(f"Unknown proof rule: {rule}")


def check_certificate(certificate):
    if not isinstance(certificate, dict) or set(certificate) != {"goal", "proof"}:
        raise CheckError("A theorem certificate has exactly goal and proof fields")
    check_proof(certificate["goal"], certificate["proof"])


def main():
    try:
        check_certificate(json.load(sys.stdin))
    except (CheckError, json.JSONDecodeError, RecursionError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    print("ACCEPT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
