"""A complete, deliberately readable checker for the BRep native calculus.

Terms: variable i (a nonnegative integer), [] (zero), [t] (successor),
       [n, a, h] (iteration; only h binds one variable).
Formulas: [s, t] (equality), [B] (D, binding y=0 and x=1),
          [0, 0, B] (Q, binding y=0).

The public driver checks closed theorems only. ``verify`` checks arbitrary
open sequents. Its n free parameters have indices 0,...,n-1; an eigenparameter
is appended at index n. Bound variables use ordinary de Bruijn indices.
All operations are syntactic: no normalization or arithmetic oracle is used.
"""

import json
import sys


class InvalidCertificate(ValueError):
    """An ill-formed expression or an invalid inference was supplied."""
    pass


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def term_ok(term, n):
    if type(term) is int:
        return 0 <= term < n
    if type(term) is not list:
        return False
    if not term:
        return True
    if len(term) == 1:
        return term_ok(term[0], n)
    if len(term) == 3:
        return (term_ok(term[0], n) and term_ok(term[1], n)
                and term_ok(term[2], n + 1))
    return False


def is_q(formula):
    return (type(formula) is list and len(formula) == 3
            and type(formula[0]) is int and formula[0] == 0
            and type(formula[1]) is int and formula[1] == 0)


def formula_ok(formula, n):
    if type(formula) is not list:
        return False
    if len(formula) == 2:
        return all(term_ok(term, n) for term in formula)
    if len(formula) == 1:
        return formula_ok(formula[0], n + 2)
    if is_q(formula):
        return formula_ok(formula[2], n + 1)
    return False


def map_term(term, on_variable, depth=0):
    if type(term) is int:
        return on_variable(term, depth)
    if not term:
        return []
    if len(term) == 1:
        return [map_term(term[0], on_variable, depth)]
    counter, seed, body = term
    return [map_term(counter, on_variable, depth),
            map_term(seed, on_variable, depth),
            map_term(body, on_variable, depth + 1)]


def map_formula(formula, on_variable, depth=0):
    if len(formula) == 2:
        return [map_term(term, on_variable, depth) for term in formula]
    if len(formula) == 1:
        return [map_formula(formula[0], on_variable, depth + 2)]
    return [0, 0, map_formula(formula[2], on_variable, depth + 1)]


def shift_term(term, amount, cutoff=0):
    return map_term(term, lambda i, d: i + amount if i >= cutoff + d else i)


def shift_formula(formula, amount, cutoff=0):
    return map_formula(formula,
                       lambda i, d: i + amount if i >= cutoff + d else i)


def substitution(image, index):
    """Remove one free slot and replace it by image, avoiding capture."""
    def on_variable(i, depth):
        slot = index + depth
        if i == slot:
            return shift_term(image, depth)
        return i - 1 if i > slot else i
    return on_variable


def substitute_term(term, image, index=0):
    return map_term(term, substitution(image, index))


def substitute_formula(formula, image, index=0):
    return map_formula(formula, substitution(image, index))


def witness_body(matrix, witness):
    """B(x,y) -> B(witness,y), keeping y as the one bound variable."""
    return substitute_formula(matrix, shift_term(witness, 1), index=1)


def replace_term(term, old, new):
    """One top-down pass, replacing all outermost matches of old by new.

    Inserted copies of new are not revisited. Under an iterator body both
    patterns are shifted; bound variables cannot be mistaken for free ones.
    """
    if term == old:
        return new
    if type(term) is int or not term:
        return term
    if len(term) == 1:
        return [replace_term(term[0], old, new)]
    counter, seed, body = term
    return [replace_term(counter, old, new),
            replace_term(seed, old, new),
            replace_term(body, shift_term(old, 1), shift_term(new, 1))]


def fields(proof, expected):
    require(type(proof) is dict and set(proof) == set(expected),
            "wrong proof-node fields")


def verify(n, context, goal, proof):
    """Raise InvalidCertificate on failure; return None on acceptance."""
    require(type(n) is int and n >= 0, "invalid parameter count")
    require(type(context) is list and all(formula_ok(a, n) for a in context),
            "ill-scoped context")
    require(formula_ok(goal, n), "ill-scoped goal")
    require(type(proof) is dict and type(proof.get("rule")) is str,
            "missing inference rule")
    rule = proof["rule"]

    if rule == "hyp":
        fields(proof, ("rule", "index"))
        index = proof["index"]
        require(type(index) is int and 0 <= index < len(context),
                "invalid hypothesis index")
        require(context[index] == goal, "hypothesis does not match goal")

    elif rule in ("i0", "is"):
        fields(proof, ("rule",))
        require(len(goal) == 2, "computation requires an equation")
        left, right = goal
        require(type(left) is list and len(left) == 3,
                "left side is not an iterator")
        counter, seed, body = left
        if rule == "i0":
            require(counter == [] and right == seed,
                    "not a zero computation equation")
        else:
            require(type(counter) is list and len(counter) == 1,
                    "iterator counter is not a successor")
            recursive_value = [counter[0], seed, body]
            require(right == substitute_term(body, recursive_value),
                    "wrong successor computation endpoint")

    elif rule == "brep":
        fields(proof, ("rule", "equality", "major", "minor"))
        equality = proof["equality"]
        require(type(equality) is list and len(equality) == 2
                and formula_ok(equality, n), "ill-scoped major equation")
        require(len(goal) == 2, "replacement requires an equation")
        source, target = equality
        result, destination = goal
        verify(n, context, equality, proof["major"])
        minor = [replace_term(destination, target, source), result]
        verify(n, context, minor, proof["minor"])

    elif rule == "qe":
        fields(proof, ("rule", "body", "term", "major", "base"))
        body, term = proof["body"], proof["term"]
        require(formula_ok(body, n + 1) and term_ok(term, n),
                "ill-scoped closure instance")
        require(goal == substitute_formula(body, term),
                "closure instance does not match goal")
        verify(n, context, [0, 0, body], proof["major"])
        verify(n, context, substitute_formula(body, []), proof["base"])

    elif rule == "de":
        fields(proof, ("rule", "matrix", "major", "branch"))
        matrix = proof["matrix"]
        require(formula_ok(matrix, n + 2), "ill-scoped D matrix")
        verify(n, context, [matrix], proof["major"])
        closure = [0, 0, witness_body(matrix, n)]
        verify(n + 1, context + [closure], goal, proof["branch"])

    elif rule == "di":
        fields(proof, ("rule", "witness", "premise"))
        require(len(goal) == 1, "case introduction requires D")
        witness = proof["witness"]
        require(term_ok(witness, n), "ill-scoped existential witness")
        body = witness_body(goal[0], witness)
        base = substitute_formula(body, [])
        step = substitute_formula(body, [n])
        verify(n + 1, context + [base], step, proof["premise"])

    elif rule == "qi":
        fields(proof, ("rule", "premise"))
        require(is_q(goal) and len(goal[2]) == 2,
                "progress introduction requires a literal equation")
        body = goal[2]
        previous = substitute_formula(body, n)
        following = substitute_formula(body, [n])
        verify(n + 1, context + [previous], following, proof["premise"])

    else:
        raise InvalidCertificate("unknown inference rule")


def check(data):
    """The public certificate format has exactly these four fields."""
    require(type(data) is dict
            and set(data) == {"n", "context", "goal", "proof"},
            "wrong certificate fields")
    require(type(data["n"]) is int and data["n"] == 0
            and data["context"] == [], "the driver accepts closed theorems only")
    verify(data["n"], data["context"], data["goal"], data["proof"])


if __name__ == "__main__":
    try:
        check(json.load(sys.stdin))
    except (InvalidCertificate, TypeError, ValueError, RecursionError) as error:
        print("REJECT: " + str(error), file=sys.stderr)
        raise SystemExit(1)
    print("ACCEPT")

