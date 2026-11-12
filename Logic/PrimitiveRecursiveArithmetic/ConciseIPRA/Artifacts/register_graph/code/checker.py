"""Standalone proof checker for counter-aware register-iterator arithmetic.

Input is one closed-theorem JSON certificate on stdin, with goal and proof.
No input is evaluated as Python.  There are no public premises or parameters.
Terms: ["v", name], ["0"], ["j", counter, index_name, state_name, body].
Only the body of j binds the two distinct names.  S(t) abbreviates
j(t; i,r.0), and 1 abbreviates S(0).  Formulas use =, bot, and, or,
imp, all, ex.  An iff is represented by a conjunction of implications.

The primitive arithmetic schemes are J0, the successor graph, separation,
and contextual induction for a literal equation.  All other rules below
are ordinary intuitionistic natural deduction and actual-equality rules.
The complete syntax validator, substitution implementation, proof checker,
JSON parser, and public driver are in this file.
"""

import json
import re
import sys


class Invalid(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def name(value):
    require(type(value) is str and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", value),
            "invalid variable name")
    return value


def term(expression, scope):
    require(type(expression) is list and expression, "term must be a nonempty list")
    tag = expression[0]
    if tag == "0":
        require(len(expression) == 1, "zero has no arguments")
    elif tag == "v":
        require(len(expression) == 2, "variable has one argument")
        require(name(expression[1]) in scope, "unbound term variable")
    elif tag == "j":
        require(len(expression) == 5, "j has four arguments")
        _, counter, index, state, body = expression
        name(index)
        name(state)
        require(index != state, "j binds two distinct variables")
        term(counter, scope)
        term(body, scope | {index, state})
    else:
        raise Invalid("unknown term constructor")


def formula(expression, scope):
    require(type(expression) is list and expression, "formula must be a nonempty list")
    tag = expression[0]
    if tag == "bot":
        require(len(expression) == 1, "bot has no arguments")
    elif tag == "=":
        require(len(expression) == 3, "equality has two terms")
        term(expression[1], scope)
        term(expression[2], scope)
    elif tag in ("and", "or", "imp"):
        require(len(expression) == 3, "binary connective has two formulas")
        formula(expression[1], scope)
        formula(expression[2], scope)
    elif tag in ("all", "ex"):
        require(len(expression) == 3, "quantifier has a variable and body")
        bound = name(expression[1])
        formula(expression[2], scope | {bound})
    else:
        raise Invalid("unknown formula constructor")


def free(expression):
    tag = expression[0]
    if tag == "v":
        return {expression[1]}
    if tag in ("0", "bot"):
        return set()
    if tag == "j":
        return free(expression[1]) | (free(expression[4]) - set(expression[2:4]))
    if tag in ("all", "ex"):
        return free(expression[2]) - {expression[1]}
    return free(expression[1]) | free(expression[2])


def names(expression):
    tag = expression[0]
    if tag == "v":
        return {expression[1]}
    if tag in ("0", "bot"):
        return set()
    if tag == "j":
        return names(expression[1]) | set(expression[2:4]) | names(expression[4])
    if tag in ("all", "ex"):
        return {expression[1]} | names(expression[2])
    return names(expression[1]) | names(expression[2])


def substitute(expression, replacements):
    """Simultaneous, capture-avoiding substitution of numerical terms."""
    tag = expression[0]
    if tag == "v":
        return replacements.get(expression[1], expression)
    if tag in ("0", "bot"):
        return expression
    if tag in ("j", "all", "ex"):
        if tag == "j":
            binders, body = list(expression[2:4]), expression[4]
        else:
            binders, body = [expression[1]], expression[2]
        active = {key: value for key, value in replacements.items() if key not in binders}
        introduced = set().union(*(free(value) for value in active.values()))
        used = names(body) | set(binders) | set(active) | introduced
        for position, bound in enumerate(binders):
            if bound in introduced:
                number = 0
                fresh = "fresh" + str(number)
                while fresh in used:
                    number += 1
                    fresh = "fresh" + str(number)
                used.add(fresh)
                body = substitute(body, {bound: ["v", fresh]})
                binders[position] = fresh
        body = substitute(body, active)
        if tag == "j":
            return ["j", substitute(expression[1], replacements), *binders, body]
        return [tag, binders[0], body]
    return [tag, substitute(expression[1], replacements),
            substitute(expression[2], replacements)]


def canonical(expression, bound=()):
    """Alpha-equivalence key; free names stay free and are not renamed."""
    tag = expression[0]
    if tag == "v":
        variable = expression[1]
        for offset, candidate in enumerate(reversed(bound)):
            if variable == candidate:
                return ("bound", offset)
        return ("free", variable)
    if tag in ("0", "bot"):
        return (tag,)
    if tag == "j":
        return (tag, canonical(expression[1], bound),
                canonical(expression[4], bound + tuple(expression[2:4])))
    if tag in ("all", "ex"):
        return (tag, canonical(expression[2], bound + (expression[1],)))
    return (tag, canonical(expression[1], bound), canonical(expression[2], bound))


def same(left, right):
    return canonical(left) == canonical(right)


def zero():
    return ["0"]


def successor(value):
    return ["j", value, "i", "r", zero()]


def one():
    return successor(zero())


def equality(left, right):
    return ["=", left, right]


def iff(left, right):
    return ["and", ["imp", left, right], ["imp", right, left]]


def step_graph(counter, index, state, body, output):
    previous = ["j", counter, index, state, body]
    instruction = substitute(body, {index: counter, state: previous})
    result = ["j", successor(counter), index, state, body]
    cases = ["or", ["and", equality(instruction, zero()),
                       equality(output, successor(previous))],
                    equality(instruction, successor(output))]
    return iff(equality(result, output), cases)


def fields(node, extra=()):
    require(set(node) == {"rule", "conclusion", *extra}, "wrong rule fields")


def fresh_name(value, scope):
    value = name(value)
    require(value not in scope, "eigenvariable is not fresh")
    return value


def check_proof(node, context, scope):
    require(type(node) is dict, "proof node must be an object")
    require("rule" in node and "conclusion" in node, "missing proof fields")
    rule, goal = node["rule"], node["conclusion"]
    require(type(rule) is str, "rule must be a string")
    formula(goal, scope)

    def premise(key, assumptions=context, variables=scope):
        return check_proof(node[key], assumptions, variables)

    def expect(actual, wanted):
        require(same(actual, wanted), "premise or conclusion does not match")

    if rule == "hyp":
        fields(node, ("index",))
        index = node["index"]
        require(type(index) is int and 0 <= index < len(context), "invalid hypothesis index")
        expect(goal, context[index])
    elif rule == "refl":
        fields(node)
        require(goal[0] == "=" and same(goal[1], goal[2]), "not a reflexive equation")
    elif rule == "j_zero":
        fields(node)
        require(goal[0] == "=" and goal[1][0] == "j", "invalid J0 axiom")
        require(goal[1][1] == zero(), "J0 counter must be zero")
        expect(goal[2], one())
    elif rule == "j_step":
        fields(node, ("counter", "index", "state", "body", "output"))
        counter, index, state = node["counter"], name(node["index"]), name(node["state"])
        require(index != state, "j binds two distinct variables")
        term(counter, scope)
        term(node["body"], scope | {index, state})
        term(node["output"], scope)
        expect(goal, step_graph(counter, index, state, node["body"], node["output"]))
    elif rule == "separation":
        fields(node)
        expect(goal, ["imp", equality(zero(), one()), ["bot"]])
    elif rule == "eq_elim":
        fields(node, ("equality", "premise", "variable", "motive"))
        equation = premise("equality")
        require(equation[0] == "=", "equality elimination requires an equation")
        variable = fresh_name(node["variable"], scope)
        motive = node["motive"]
        formula(motive, scope | {variable})
        expect(premise("premise"), substitute(motive, {variable: equation[1]}))
        expect(goal, substitute(motive, {variable: equation[2]}))
    elif rule == "imp_intro":
        fields(node, ("proof",))
        require(goal[0] == "imp", "implication introduction requires an implication")
        expect(premise("proof", context + [goal[1]]), goal[2])
    elif rule == "imp_elim":
        fields(node, ("implication", "argument"))
        implication = premise("implication")
        require(implication[0] == "imp", "not an implication")
        expect(premise("argument"), implication[1])
        expect(goal, implication[2])
    elif rule == "and_intro":
        fields(node, ("left", "right"))
        require(goal[0] == "and", "conjunction introduction requires a conjunction")
        expect(premise("left"), goal[1])
        expect(premise("right"), goal[2])
    elif rule in ("and_left", "and_right"):
        fields(node, ("proof",))
        conjunction = premise("proof")
        require(conjunction[0] == "and", "not a conjunction")
        expect(goal, conjunction[1 if rule == "and_left" else 2])
    elif rule in ("or_left", "or_right"):
        fields(node, ("proof",))
        require(goal[0] == "or", "disjunction introduction requires a disjunction")
        expect(premise("proof"), goal[1 if rule == "or_left" else 2])
    elif rule == "or_elim":
        fields(node, ("disjunction", "left", "right"))
        disjunction = premise("disjunction")
        require(disjunction[0] == "or", "not a disjunction")
        expect(premise("left", context + [disjunction[1]]), goal)
        expect(premise("right", context + [disjunction[2]]), goal)
    elif rule == "all_intro":
        fields(node, ("eigen", "proof"))
        require(goal[0] == "all", "universal introduction requires a universal")
        eigen = fresh_name(node["eigen"], scope)
        instance = substitute(goal[2], {goal[1]: ["v", eigen]})
        expect(premise("proof", context, scope | {eigen}), instance)
    elif rule == "all_elim":
        fields(node, ("universal", "term"))
        universal = premise("universal")
        require(universal[0] == "all", "not a universal")
        term(node["term"], scope)
        expect(goal, substitute(universal[2], {universal[1]: node["term"]}))
    elif rule == "ex_intro":
        fields(node, ("witness", "proof"))
        require(goal[0] == "ex", "existential introduction requires an existential")
        term(node["witness"], scope)
        expect(premise("proof"), substitute(goal[2], {goal[1]: node["witness"]}))
    elif rule == "ex_elim":
        fields(node, ("existential", "eigen", "proof"))
        existential = premise("existential")
        require(existential[0] == "ex", "not an existential")
        eigen = fresh_name(node["eigen"], scope)
        instance = substitute(existential[2], {existential[1]: ["v", eigen]})
        expect(premise("proof", context + [instance], scope | {eigen}), goal)
    elif rule == "absurd":
        fields(node, ("proof",))
        expect(premise("proof"), ["bot"])
    elif rule == "induction":
        fields(node, ("variable", "equation", "term", "eigen", "base", "step"))
        variable = fresh_name(node["variable"], scope)
        equation = node["equation"]
        formula(equation, scope | {variable})
        require(equation[0] == "=", "induction is restricted to literal equations")
        term(node["term"], scope)
        eigen = fresh_name(node["eigen"], scope)
        current = substitute(equation, {variable: ["v", eigen]})
        following = substitute(equation, {variable: successor(["v", eigen])})
        expect(premise("base"), substitute(equation, {variable: zero()}))
        expect(premise("step", context + [current], scope | {eigen}), following)
        expect(goal, substitute(equation, {variable: node["term"]}))
    else:
        raise Invalid("unknown inference rule")
    return goal


def check_certificate(certificate):
    require(type(certificate) is dict, "certificate must be an object")
    require(set(certificate) == {"goal", "proof"},
            "wrong certificate fields")
    formula(certificate["goal"], set())
    conclusion = check_proof(certificate["proof"], [], set())
    require(same(conclusion, certificate["goal"]), "advertised goal differs from proof")
    return True


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON object key")
        result[key] = value
    return result


def forbidden_constant(value):
    raise Invalid("nonstandard JSON numeric constant")


def main():
    try:
        certificate = json.loads(sys.stdin.read(), object_pairs_hook=unique_object,
                                 parse_constant=forbidden_constant)
        check_certificate(certificate)
    except (Invalid, ValueError, RecursionError) as error:
        print("REJECT:", error)
        return 1
    print("ACCEPT")
    return 0


if __name__ == "__main__":
    sys.exit(main())
