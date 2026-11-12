"""Complete proof checker for the four-schema G/J presentation of iPRA.

The public input is a JSON object with exactly ``goal`` and ``proof``.
No evaluator, proof search, arithmetic library, or untrusted producer is
imported. Ordinary Python/JSON resource limits may reject large proofs.
See FORMAT.txt for the complete syntax and inference rules.
"""
import json


def require(condition):
    if not condition:
        raise ValueError("invalid certificate")


def node(value, size):
    require(type(value) is list and len(value) == size)


def term(value, depth, scope):
    if type(value) is int and value == 0:
        return
    require(type(value) is list and len(value) > 0)
    tag = value[0]
    if tag == "v":
        node(value, 2)
        require(type(value[1]) is int and 0 <= value[1] < depth)
    elif tag == "p":
        node(value, 2)
        require(type(value[1]) is str and value[1] in scope)
    elif tag == "g":
        node(value, 3)
        term(value[1], depth, scope)
        term(value[2], depth, scope)
    elif tag == "j":
        node(value, 3)
        term(value[1], depth, scope)
        term(value[2], depth + 1, scope)
    else:
        raise ValueError("unknown numerical constructor")


def formula(value, depth, scope):
    require(type(value) is list and len(value) > 0)
    tag = value[0]
    if tag == "=":
        node(value, 3)
        term(value[1], depth, scope)
        term(value[2], depth, scope)
    elif tag == "q":
        node(value, 2)
        formula(value[1], depth + 1, scope)
    elif tag == "d":
        node(value, 2)
        formula(value[1], depth + 2, scope)
    else:
        raise ValueError("unknown formula constructor")


def replace(value, images, level=0):
    """Simultaneously open the next len(images) numerical binder slots.

    Images are inserted without traversing them again. Their free bound
    coordinates are shifted under the internal binders being traversed.
    The one deliberately open image used by DE is v(0), retained under Q.
    """
    if value == 0:
        return 0
    tag = value[0]
    if tag == "p":
        return value
    if tag == "v":
        index = value[1]
        if index < level:
            return value
        if index < level + len(images):
            return shift(images[index - level], level)
        return ["v", index - len(images)]
    if tag in ("g", "="):
        return [tag, replace(value[1], images, level),
                replace(value[2], images, level)]
    if tag == "j":
        return [tag, replace(value[1], images, level),
                replace(value[2], images, level + 1)]
    return [tag, replace(value[1], images, level + (1 if tag == "q" else 2))]


def shift(value, amount, level=0):
    """Lift the free de Bruijn coordinates of a numerical image."""
    if value == 0 or value[0] == "p":
        return value
    tag = value[0]
    if tag == "v":
        return [tag, value[1] + (amount if value[1] >= level else 0)]
    return [tag, shift(value[1], amount, level),
            shift(value[2], amount, level + (tag == "j"))]


def successor(value):
    return ["g", 0, value]


def computation(equation):
    require(equation[0] == "=")
    left, right = equation[1:]
    require(type(left) is list)
    if left[0] == "g":
        first = left[1]
        if not (type(first) is list and first[0] == "g" and first[1] == 0):
            return False
        code = first[2]
        decode = type(code) is list and code[0] == "g" and code[1] == 0
        if decode:
            code = code[2]
        return (type(code) is list and code[0] == "j"
                and code[2] == successor(successor(["v", 0]))
                and right == (code[1] if decode else left[2]))
    if left[0] == "j":
        counter, body = left[1:]
        if counter == 0:
            return right == 0
        return (type(counter) is list and counter[0] == "g"
                and counter[1] == 0
                and right == replace(body, [["j", counter[2], body]]))
    return False


def check(proof, scope, context):
    require(type(proof) is list and len(proof) > 0)
    rule = proof[0]
    if rule == "hyp":
        node(proof, 2)
        require(type(proof[1]) is int and 0 <= proof[1] < len(context))
        return context[proof[1]]
    if rule == "ax":
        node(proof, 2)
        formula(proof[1], 0, scope)
        require(computation(proof[1]))
        return proof[1]
    if rule == "di":
        node(proof, 6)
        target, witness, name, mode, premise = proof[1:]
        formula(target, 0, scope)
        require(target[0] == "d")
        term(witness, 0, scope)
        require(type(name) is str and name not in scope)
        body = target[1]
        require(mode == "case" or mode == "step" and body[0] == "=")
        parameter = ["p", name]
        local = replace(body, [0 if mode == "case" else parameter, witness])
        expected = replace(body, [successor(parameter), witness])
        require(check(premise, scope | {name}, context + [local]) == expected)
        return target
    if rule == "qe":
        node(proof, 4)
        major = check(proof[1], scope, context)
        require(major[0] == "q")
        term(proof[2], 0, scope)
        require(check(proof[3], scope, context) == replace(major[1], [0]))
        return replace(major[1], [proof[2]])
    if rule == "de":
        node(proof, 5)
        major = check(proof[1], scope, context)
        require(major[0] == "d")
        name, target = proof[2:4]
        require(type(name) is str and name not in scope)
        formula(target, 0, scope)
        local = ["q", replace(major[1], [["v", 0], ["p", name]])]
        require(check(proof[4], scope | {name}, context + [local]) == target)
        return target
    if rule == "tr":
        node(proof, 4)
        major = check(proof[1], scope, context)
        require(major[0] == "=")
        formula(proof[2], 1, scope)
        require(check(proof[3], scope, context) == replace(proof[2], [major[1]]))
        return replace(proof[2], [major[2]])
    raise ValueError("unknown inference rule")


def verify(packet):
    require(type(packet) is dict and set(packet) == {"goal", "proof"})
    formula(packet["goal"], 0, set())
    require(check(packet["proof"], set(), []) == packet["goal"])
    return True


if __name__ == "__main__":
    try:
        verify(json.load(open(0)))
        print("ACCEPT")
    except Exception:
        print("REJECT")
        raise SystemExit(1)
