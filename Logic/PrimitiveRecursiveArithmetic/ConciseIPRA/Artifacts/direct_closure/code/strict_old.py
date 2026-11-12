"""Standalone checker for the witnessed-D native iPRA presentation.

Input is a JSON object with parameters, context, goal, and proof fields.
All syntax and scopes are checked. Only a successful run prints ACCEPT.
No certificate text is evaluated as Python. Assertions are not used.
"""
import json

SIGNATURE = {
    "z": ("term", ()),
    "s": ("term", (("term", 0),)),
    "i": ("term", (("term", 0), ("term", 0), ("term", 1))),
    "e": ("formula", (("term", 0), ("term", 0))),
    "q": ("formula", (("formula", 1),)),
    "d": ("formula", (("formula", 2),)),
}
ZERO = ["z"]

def require(condition):
    if not condition:
        raise ValueError("invalid certificate")

def variable(index):
    return ["v", index]

def validate(expression, sort, scope):
    require(type(expression) is list and bool(expression))
    tag = expression[0]
    require(type(tag) is str)
    if tag == "v":
        require(sort == "term" and len(expression) == 2)
        index = expression[1]
        require(type(index) is int and 0 <= index < scope)
        return
    require(tag in SIGNATURE)
    expected_sort, children = SIGNATURE[tag]
    require(sort == expected_sort and len(expression) == len(children) + 1)
    for child, (child_sort, bound) in zip(expression[1:], children):
        validate(child, child_sort, scope + bound)

def substitute(expression, images):
    if expression[0] == "v":
        return images(expression[1])
    children = SIGNATURE[expression[0]][1]
    return [expression[0]] + [
        substitute(child, lift(images, bound))
        for child, (_, bound) in zip(expression[1:], children)
    ]

def lift(images, bound):
    return lambda index: (variable(index) if index < bound
                          else shift(images(index - bound), bound))

def shift(expression, amount=1):
    return substitute(expression, lambda index: variable(index + amount))

def instantiate(expression, term):
    return substitute(expression, lambda index: term if index == 0
                      else variable(index - 1))

def successor_instance(expression):
    return substitute(expression, lambda index: ["s", variable(0)]
                      if index == 0 else variable(index))

def witness_instance(matrix, witness):
    return substitute(matrix, lambda index: variable(0) if index == 0
                      else shift(witness) if index == 1
                      else variable(index - 1))

def derive(proof, context, scope):
    require(type(proof) is list and bool(proof))
    rule, *arguments = proof
    shifted_context = [shift(formula) for formula in context]
    if rule == "hyp":
        index, = arguments
        require(type(index) is int and 0 <= index < len(context))
        return context[index]
    if rule == "zero":
        seed, update = arguments
        validate(seed, "term", scope)
        validate(update, "term", scope + 1)
        return ["e", ["i", ZERO, seed, update], seed]
    if rule == "succ":
        counter, seed, update = arguments
        validate(counter, "term", scope)
        validate(seed, "term", scope)
        validate(update, "term", scope + 1)
        source = ["i", ["s", counter], seed, update]
        result = instantiate(update, ["i", counter, seed, update])
        return ["e", source, result]
    if rule == "tr":
        template, equality_proof, instance_proof = arguments
        validate(template, "formula", scope + 1)
        equality = derive(equality_proof, context, scope)
        require(equality[0] == "e")
        require(derive(instance_proof, context, scope)
                == instantiate(template, equality[1]))
        return instantiate(template, equality[2])
    if rule == "qe":
        term, closure_proof, base_proof = arguments
        validate(term, "term", scope)
        closure = derive(closure_proof, context, scope)
        require(closure[0] == "q")
        require(derive(base_proof, context, scope)
                == instantiate(closure[1], ZERO))
        return instantiate(closure[1], term)
    if rule == "de":
        conclusion, major_proof, branch_proof = arguments
        validate(conclusion, "formula", scope)
        major = derive(major_proof, context, scope)
        require(major[0] == "d")
        branch_context = [["q", major[1]]] + shifted_context
        require(derive(branch_proof, branch_context, scope + 1)
                == shift(conclusion))
        return conclusion
    if rule == "case":
        matrix, witness, branch_proof = arguments
        validate(matrix, "formula", scope + 2)
        validate(witness, "term", scope)
        body = witness_instance(matrix, witness)
        branch_context = [shift(instantiate(body, ZERO))] + shifted_context
        require(derive(branch_proof, branch_context, scope + 1)
                == successor_instance(body))
        return ["d", matrix]
    if rule == "prog":
        matrix, witness, branch_proof = arguments
        validate(matrix, "formula", scope + 2)
        require(matrix[0] == "e")
        validate(witness, "term", scope)
        body = witness_instance(matrix, witness)
        branch_context = [body] + shifted_context
        require(derive(branch_proof, branch_context, scope + 1)
                == successor_instance(body))
        return ["d", matrix]
    raise ValueError("unknown rule")

def check(document):
    scope = document["parameters"]
    context = document["context"]
    goal = document["goal"]
    require(type(scope) is int and scope >= 0 and type(context) is list)
    for formula in context:
        validate(formula, "formula", scope)
    validate(goal, "formula", scope)
    require(derive(document["proof"], context, scope) == goal)

if __name__ == "__main__":
    check(json.load(open(0)))
    print("ACCEPT")
