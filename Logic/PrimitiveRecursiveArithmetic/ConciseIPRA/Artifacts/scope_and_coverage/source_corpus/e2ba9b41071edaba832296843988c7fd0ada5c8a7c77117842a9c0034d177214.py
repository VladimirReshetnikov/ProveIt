"""Readable affine/uniform predecessor verifier.

This is a standalone explanation, not imported by any measured checker.
It uses an explicit list predicate. Success means exit zero and ACCEPT;
any exception rejects. Terms/formulas are interpreted by the sorted codec.
"""
from json import load

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    if isinstance(tree, list):
        return [open_tree(child, image, depth + len(tree) + 1)
                for child in tree]
    if fresh_floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=1)
    return 0


def verify(goal, assumptions):
    global fresh_floor
    if open_tree(goal) in assumptions:
        return
    major, source, target, template = instruction()
    if major:
        verify(major, assumptions)
        if (major in ([source, target], not source and [template])
                and open_tree(template, target) == goal):
            candidate = open_tree(template, source)
            if candidate:
                goal = candidate
        new_assumption = major[2:]
    elif major is None:
        predecessor, seed, update = source, target, template
        counter = [predecessor] if predecessor else predecessor
        recursive_value = [predecessor, seed, update]
        result = (open_tree(update, recursive_value, 1)
                  if predecessor else seed)
        new_assumption = [[counter, seed, update], result]
    else:
        # Exact D arity is required. In this encoding high arity formulas
        # denote the fixed contradiction, so they must not enter this rule.
        annotation0, annotation1, matrix = goal
        new_assumption = goal = open_tree(matrix, template, 2)
    fresh_floor -= 1
    hypothesis_image = (fresh_floor
                        if major or len(goal) % 2 == major else 0)
    verify(open_tree(goal, [fresh_floor]),
           assumptions + [open_tree(new_assumption, hypothesis_image)])


instruction = load(open(0)).pop
verify(instruction(), [])
print('ACCEPT')
