"""Standalone natural-deduction checker for a self-seeded arithmetic theory.

Input: exactly {"goal": closed_formula, "proof": proof_tree} as JSON.
Success: normal exit and ACCEPT. Any failed check or malformed data rejects.
Bound variables are de Bruijn indices; named free parameters are scoped by
proof rules. The complete nonlogical axiom inventory is in axiom().
"""
import json
import sys

ZERO = ["0"]
ONE = ["S", ZERO]
FALSE = ["false"]


def require(condition):
    if not condition:
        raise ValueError("Invalid certificate")


def well_formed(tree, sort, parameters, depth=0):
    if type(tree) is not list or not tree or type(tree[0]) is not str:
        return False
    tag, *parts = tree
    if sort == "term":
        if tag == "0":
            return not parts
        if tag == "v":
            return len(parts) == 1 and type(parts[0]) is str and parts[0] in parameters
        if tag == "b":
            return len(parts) == 1 and type(parts[0]) is int and 0 <= parts[0] < depth
        if tag == "S":
            return len(parts) == 1 and well_formed(parts[0], "term", parameters, depth)
        if tag == "e":
            return len(parts) == 2 and all(well_formed(t, "term", parameters, depth) for t in parts)
        if tag == "F":
            return len(parts) == 2 and well_formed(parts[0], "term", parameters, depth) and well_formed(parts[1], "term", parameters, depth + 1)
    if sort == "formula":
        if tag == "false":
            return not parts
        if tag == "=":
            return len(parts) == 2 and all(well_formed(t, "term", parameters, depth) for t in parts)
        if tag in ("and", "or", "imp"):
            return len(parts) == 2 and all(well_formed(t, "formula", parameters, depth) for t in parts)
        if tag in ("all", "ex"):
            return len(parts) == 1 and well_formed(parts[0], "formula", parameters, depth + 1)
    return False


def term(tree, parameters, depth=0):
    require(well_formed(tree, "term", parameters, depth))
    return tree


def formula(tree, parameters, depth=0):
    require(well_formed(tree, "formula", parameters, depth))
    return tree


def instantiate(tree, image, depth=0):
    """Remove one outer bound slot, inserting a root-closed term image."""
    tag = tree[0]
    if tag == "b":
        index = tree[1]
        return image if index == depth else ["b", index - (index > depth)]
    if tag == "F":
        return ["F", instantiate(tree[1], image, depth), instantiate(tree[2], image, depth + 1)]
    if tag in ("all", "ex"):
        return [tag, instantiate(tree[1], image, depth + 1)]
    return [instantiate(part, image, depth) if type(part) is list else part for part in tree]


def abstract(tree, name, depth=0):
    """Bind one named free parameter outside the whole expression."""
    if tree == ["v", name]:
        return ["b", depth]
    tag = tree[0]
    if tag == "F":
        return ["F", abstract(tree[1], name, depth), abstract(tree[2], name, depth + 1)]
    if tag in ("all", "ex"):
        return [tag, abstract(tree[1], name, depth + 1)]
    return [abstract(part, name, depth) if type(part) is list else part for part in tree]


def free_parameters(tree):
    if tree[0] == "v":
        return {tree[1]}
    return set().union(*(free_parameters(part) for part in tree if type(part) is list))


def fresh(name, parameters):
    require(type(name) is str and bool(name) and name not in parameters)
    return parameters | {name}


def axiom(packet, parameters):
    name, *parts = packet
    if name == "F0":
        body, = parts
        term(body, parameters, 1)
        return ["=", ["F", ZERO, body], ["S", instantiate(body, ZERO)]]
    if name == "FS":
        counter, body = parts
        term(counter, parameters)
        term(body, parameters, 1)
        return ["=", ["F", ["S", counter], body], instantiate(body, ["F", counter, body])]
    if name in ("range", "reflection"):
        left, right = parts
        term(left, parameters)
        term(right, parameters)
        truth = ["=", ["e", left, right], ONE]
        if name == "range":
            return ["or", ["=", ["e", left, right], ZERO], truth]
        equality = ["=", left, right]
        return ["and", ["imp", truth, equality], ["imp", equality, truth]]
    if name == "separation":
        require(not parts)
        return ["imp", ["=", ZERO, ONE], FALSE]
    if name == "injectivity":
        left, right = parts
        term(left, parameters)
        term(right, parameters)
        return ["imp", ["=", ["S", left], ["S", right]], ["=", left, right]]
    raise ValueError("Unknown nonlogical axiom")


def prove(proof, context=(), parameters=frozenset()):
    require(type(proof) is list and bool(proof))
    rule, *parts = proof
    if rule == "hyp":
        index, = parts
        require(type(index) is int and 0 <= index < len(context))
        return context[index]
    if rule == "axiom":
        return axiom(parts, parameters)
    if rule == "refl":
        value, = parts
        term(value, parameters)
        return ["=", value, value]
    if rule == "replace":
        equality_proof, template, instance_proof = parts
        equality = prove(equality_proof, context, parameters)
        require(equality[0] == "=")
        formula(template, parameters, 1)
        require(prove(instance_proof, context, parameters) == instantiate(template, equality[1]))
        return instantiate(template, equality[2])
    if rule == "andI":
        left, right = parts
        return ["and", prove(left, context, parameters), prove(right, context, parameters)]
    if rule in ("andL", "andR"):
        premise, = parts
        result = prove(premise, context, parameters)
        require(result[0] == "and")
        return result[1 if rule == "andL" else 2]
    if rule == "orL":
        premise, right = parts
        formula(right, parameters)
        return ["or", prove(premise, context, parameters), right]
    if rule == "orR":
        left, premise = parts
        formula(left, parameters)
        return ["or", left, prove(premise, context, parameters)]
    if rule == "orE":
        major, left, right = parts
        disjunction = prove(major, context, parameters)
        require(disjunction[0] == "or")
        result = prove(left, context + (disjunction[1],), parameters)
        require(prove(right, context + (disjunction[2],), parameters) == result)
        return result
    if rule == "impI":
        assumption, body = parts
        formula(assumption, parameters)
        return ["imp", assumption, prove(body, context + (assumption,), parameters)]
    if rule == "impE":
        major, minor = parts
        implication = prove(major, context, parameters)
        require(implication[0] == "imp")
        require(prove(minor, context, parameters) == implication[1])
        return implication[2]
    if rule == "falseE":
        goal, premise = parts
        formula(goal, parameters)
        require(prove(premise, context, parameters) == FALSE)
        return goal
    if rule == "allI":
        name, body = parts
        extended = fresh(name, parameters)
        return ["all", abstract(prove(body, context, extended), name)]
    if rule == "allE":
        premise, value = parts
        universal = prove(premise, context, parameters)
        require(universal[0] == "all")
        term(value, parameters)
        return instantiate(universal[1], value)
    if rule == "exI":
        template, witness, premise = parts
        formula(template, parameters, 1)
        term(witness, parameters)
        require(prove(premise, context, parameters) == instantiate(template, witness))
        return ["ex", template]
    if rule == "exE":
        major, name, body = parts
        existential = prove(major, context, parameters)
        require(existential[0] == "ex")
        extended = fresh(name, parameters)
        result = prove(body, context + (instantiate(existential[1], ["v", name]),), extended)
        require(name not in free_parameters(result))
        return result
    if rule == "ind":
        equation, target, base, name, step = parts
        formula(equation, parameters, 1)
        require(equation[0] == "=")
        term(target, parameters)
        require(prove(base, context, parameters) == instantiate(equation, ZERO))
        extended = fresh(name, parameters)
        parameter = ["v", name]
        hypothesis = instantiate(equation, parameter)
        require(prove(step, context + (hypothesis,), extended) == instantiate(equation, ["S", parameter]))
        return instantiate(equation, target)
    raise ValueError("Unknown inference rule")


def main():
    certificate = json.load(sys.stdin)
    require(type(certificate) is dict and set(certificate) == {"goal", "proof"})
    goal = formula(certificate["goal"], frozenset())
    require(prove(certificate["proof"]) == goal)
    print("ACCEPT")


if __name__ == "__main__":
    main()
