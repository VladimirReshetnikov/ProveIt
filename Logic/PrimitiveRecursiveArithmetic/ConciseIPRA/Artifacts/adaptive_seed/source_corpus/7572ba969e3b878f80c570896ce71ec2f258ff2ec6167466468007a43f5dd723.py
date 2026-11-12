"""Complete native Choice-DI proof checker for the three-schema B,J basis.

Only json is imported. See FORMAT.txt for all syntax, inference rules,
scoping conditions, and interpretation/evidence limits. This readable
standalone program is measured in full, including its public driver.
"""
import json

ZERO = "0"

def successor(term):
    return ["b", ZERO, term]

def successor_argument(term):
    if isinstance(term, list) and len(term) == 3 and term[:2] == ["b", ZERO]:
        return term[2]
    return None

def valid_term(term, depth, available):
    if term == ZERO:
        return True
    if not isinstance(term, list):
        return False
    if len(term) == 2 and term[0] == "v":
        index = term[1]
        return type(index) is int and (0 <= index < depth or index in available)
    if len(term) != 3:
        return False
    tag, left, right = term
    if tag == "b":
        return valid_term(left, depth, available) and valid_term(right, depth, available)
    if tag == "j":
        return valid_term(left, depth, available) and valid_term(right, depth + 1, available)
    return False

def valid_formula(formula, depth, available):
    if not isinstance(formula, list):
        return False
    if len(formula) == 3 and formula[0] == "=":
        return valid_term(formula[1], depth, available) and valid_term(formula[2], depth, available)
    if len(formula) == 2 and formula[0] in ("q", "d"):
        return valid_formula(formula[1], depth + (1 if formula[0] == "q" else 2), available)
    return False

def opening(tree, image, index=0, depth=0):
    """Remove one free slot; image has no free nonnegative coordinates.

All callers validate that premise. Internal binders of image are retained;
there are no free positive indices to lift when inserting it under binders.
"""
    if tree == ZERO:
        return ZERO
    tag = tree[0]
    if tag == "v":
        coordinate = tree[1]
        if coordinate == index + depth:
            return image
        return ["v", coordinate - (coordinate > index + depth)]
    if tag in ("b", "="):
        return [tag, opening(tree[1], image, index, depth), opening(tree[2], image, index, depth)]
    if tag == "j":
        return [tag, opening(tree[1], image, index, depth), opening(tree[2], image, index, depth + 1)]
    return [tag, opening(tree[1], image, index, depth + (1 if tag == "q" else 2))]

def computation(goal):
    if goal[0] != "=":
        return False
    left, right = goal[1:]
    if not isinstance(left, list):
        return False
    if left[0] == "j":
        counter, update = left[1:]
        if counter == ZERO:
            return right == ZERO
        previous = successor_argument(counter)
        return previous is not None and right == opening(update, ["j", previous, update])
    if left[0] == "b":
        previous = successor_argument(left[1])
        return previous is not None and right == previous
    return False

def fresh(parameter, available):
    return type(parameter) is int and parameter < 0 and parameter not in available

def check(goal, proof, context=(), available=frozenset()):
    if not valid_formula(goal, 0, available) or not isinstance(proof, list) or not proof:
        return False
    rule = proof[0]
    if rule == "hyp" and len(proof) == 2:
        index = proof[1]
        return type(index) is int and 0 <= index < len(context) and context[index] == goal
    if rule == "compute" and len(proof) == 1:
        return computation(goal)
    if rule == "di" and len(proof) == 5:
        mode, witness, parameter, step = proof[1:]
        if goal[0] != "d" or mode not in ("case", "ind"):
            return False
        if not valid_term(witness, 0, available) or not fresh(parameter, available):
            return False
        matrix = opening(goal[1], witness, 1)
        if mode == "ind" and matrix[0] != "=":
            return False
        variable = ["v", parameter]
        assumption = opening(matrix, variable if mode == "ind" else ZERO)
        conclusion = opening(matrix, successor(variable))
        return check(conclusion, step, context + (assumption,), available | {parameter})
    if rule == "de" and len(proof) == 5:
        body, parameter, major, continuation = proof[1:]
        if not valid_formula(body, 2, available) or not fresh(parameter, available):
            return False
        if not check(["d", body], major, context, available):
            return False
        assumption = ["q", opening(body, ["v", parameter], 1)]
        return check(goal, continuation, context + (assumption,), available | {parameter})
    if rule == "qe" and len(proof) == 5:
        body, target, major, minor = proof[1:]
        if not valid_formula(body, 1, available) or not valid_term(target, 0, available):
            return False
        return (opening(body, target) == goal
                and check(["q", body], major, context, available)
                and check(opening(body, ZERO), minor, context, available))
    if rule == "tr" and len(proof) == 6:
        source, target, motive, major, minor = proof[1:]
        if not valid_term(source, 0, available) or not valid_term(target, 0, available):
            return False
        if not valid_formula(motive, 1, available):
            return False
        return (opening(motive, target) == goal
                and check(["=", source, target], major, context, available)
                and check(opening(motive, source), minor, context, available))
    return False

try:
    packet = json.load(open(0))
    if not isinstance(packet, dict) or set(packet) != {"goal", "proof"}:
        raise ValueError("Expected goal and proof")
    if not check(packet["goal"], packet["proof"]):
        raise ValueError("Invalid derivation")
    print("ACCEPT")
except Exception:
    print("REJECT")
    raise SystemExit(1)
