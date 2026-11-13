"""Standalone six-rule checker with atomic-seed zero contraction.

Every rule carries raw metadata. Its complete premises and conclusion are
normalized only AFTER the specified capture-avoiding substitutions.
Input: {"goal": closed raw formula, "proof": tagged proof tree}.
Normal exit and exactly ACCEPT followed by LF means acceptance.
"""
import json
import sys


# Child sorts and numbers of additional binders.
SIGNATURE = {
    "z": ("t", ()),
    "s": ("t", (("t", 0),)),
    "i": ("t", (("t", 0), ("t", 0), ("t", 1))),
    "=": ("f", (("t", 0), ("t", 0))),
    "q": ("f", (("f", 1),)),
    "d": ("f", (("f", 2),)),
}
ZERO = ["z"]


def require(condition):
    if not condition:
        raise ValueError("invalid certificate")


def variable(index):
    return ["v", index]


def validate(tree, sort, scope):
    require(type(tree) is list and len(tree) > 0)
    tag = tree[0]
    require(type(tag) is str)
    if tag == "v":
        require(sort == "t" and len(tree) == 2)
        require(type(tree[1]) is int and 0 <= tree[1] < scope)
        return
    require(tag in SIGNATURE)
    actual_sort, children = SIGNATURE[tag]
    require(sort == actual_sort and len(tree) == len(children) + 1)
    for child, (child_sort, bound) in zip(tree[1:], children):
        validate(child, child_sort, scope + bound)


def shift(tree, amount=1, cutoff=0):
    if tree[0] == "v":
        return variable(tree[1] + amount if tree[1] >= cutoff else tree[1])
    return [tree[0]] + [
        shift(child, amount, cutoff + bound)
        for child, (_, bound) in zip(tree[1:], SIGNATURE[tree[0]][1])
    ]


def substitute(tree, images, depth=0):
    """Remove the front len(images) variables, inserting images once."""
    if tree[0] == "v":
        index = tree[1]
        if index < depth:
            return tree
        if index - depth < len(images):
            return shift(images[index - depth], depth)
        return variable(index - len(images))
    return [tree[0]] + [
        substitute(child, images, depth + bound)
        for child, (_, bound) in zip(tree[1:], SIGNATURE[tree[0]][1])
    ]


def normalize(tree):
    """Only I(0,a;h) with NORMALIZED atomic a is contracted."""
    if tree[0] == "v":
        return tree
    result = [tree[0]] + [normalize(child) for child in tree[1:]]
    if result[0] == "i" and result[1] == ZERO and result[2][0] in ("v", "z"):
        return result[2]
    return result


def derive(proof, context, scope):
    require(type(proof) is list and len(proof) > 0)
    tag = proof[0]
    require(type(tag) is str)

    if tag == "hyp" and len(proof) == 2:
        index = proof[1]
        require(type(index) is int and 0 <= index < len(context))
        return context[index]

    if tag == "step" and len(proof) == 4:
        counter, seed, update = proof[1:]
        validate(counter, "t", scope)
        validate(seed, "t", scope)
        validate(update, "t", scope + 1)
        left = ["i", ["s", counter], seed, update]
        right = substitute(update, [["i", counter, seed, update]])
        return normalize(["=", left, right])

    if tag == "tr" and len(proof) == 7:
        source, target, template, right, equality, minor = proof[1:]
        validate(source, "t", scope)
        validate(target, "t", scope)
        validate(template, "t", scope + 1)
        validate(right, "t", scope)
        require(derive(equality, context, scope) == normalize(["=", source, target]))
        require(derive(minor, context, scope) ==
                normalize(["=", substitute(template, [source]), right]))
        return normalize(["=", right, substitute(template, [target])])

    if tag == "qe" and len(proof) == 5:
        body, target, major, base = proof[1:]
        validate(body, "f", scope + 1)
        validate(target, "t", scope)
        require(derive(major, context, scope) == normalize(["q", body]))
        require(derive(base, context, scope) == normalize(substitute(body, [ZERO])))
        return normalize(substitute(body, [target]))

    if tag == "open" and len(proof) == 5:
        matrix, goal, major, branch = proof[1:]
        validate(matrix, "f", scope + 2)
        validate(goal, "f", scope)
        require(derive(major, context, scope) == normalize(["d", matrix]))
        # Within this Q, its y is index 0 and the fresh witness b is index 1.
        extended = [shift(formula) for formula in context] + [normalize(["q", matrix])]
        require(derive(branch, extended, scope + 1) == normalize(shift(goal)))
        return normalize(goal)

    if tag == "intro" and len(proof) == 4:
        matrix, witness, branch = proof[1:]
        validate(matrix, "f", scope + 2)
        validate(witness, "t", scope)
        # This is a RAW syntactic test, before normalization.
        eta = variable(0) if matrix[0] == "=" and witness == ZERO else ZERO
        lifted_matrix = shift(matrix, 1, 2)
        lifted_witness = shift(witness)
        hypothesis = substitute(lifted_matrix, [eta, lifted_witness])
        target = substitute(lifted_matrix, [["s", variable(0)], lifted_witness])
        extended = [shift(formula) for formula in context] + [normalize(hypothesis)]
        require(derive(branch, extended, scope + 1) == normalize(target))
        return normalize(["d", matrix])

    raise ValueError("unknown rule or wrong proof-node arity")


def check(document):
    require(type(document) is dict and set(document) == {"goal", "proof"})
    validate(document["goal"], "f", 0)
    require(derive(document["proof"], [], 0) == normalize(document["goal"]))


if __name__ == "__main__":
    try:
        check(json.load(sys.stdin))
    except Exception:
        sys.exit(1)
    print("ACCEPT")
