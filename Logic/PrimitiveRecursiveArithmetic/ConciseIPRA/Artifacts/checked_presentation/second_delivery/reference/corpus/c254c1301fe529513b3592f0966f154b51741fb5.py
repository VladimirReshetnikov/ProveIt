"""Standalone readable checker for the 502-byte presentation.

This companion additionally validates exact integer/list JSON values and the
closed guarded public grammar. Its full size is measured separately. It is
not an uncounted dependency of either compact program. Exceptions reject;
acceptance is normal exit with exactly ACCEPT followed by a newline.
"""
import json


def integer_list_tree(value):
    return type(value) is int or (
        type(value) is list and all(integer_list_tree(x) for x in value)
    )


def public_term(tree, slots):
    if type(tree) is int:
        return tree == 0 or (3 <= tree < 3 + 2 * slots and tree % 2 == 1)
    return type(tree) is list and (
        len(tree) == 1 and public_term(tree[0], slots + 2)
        or len(tree) == 3 and all(public_term(x, slots + 1) for x in tree)
    )


def public_formula(tree, slots=0):
    if type(tree) is not list:
        return False
    if len(tree) == 2:
        return all(public_term(x, slots) for x in tree)
    if len(tree) != 1 or not public_formula(tree[0], slots + 2):
        return False
    matrix = tree[0]
    return len(matrix) == 1 or all(
        type(side) is list and len(side) == 3 and side[:2] == [5, 0]
        for side in matrix
    )


def check(goal, context=(0,), floor=0):
    missing = object()

    def opening(tree, image=missing, depth=0):
        if type(tree) is list:
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if type(tree) is not int:
            raise ValueError("A numerical hole has no valid image")
        if floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)

    if opening(goal) in context:
        return

    major, source, initializer, template = instructions.pop()
    check(major, context, floor)

    if major:
        hypothesis = major * 3
    elif initializer:
        counter = source and [source]
        recursive = [source, initializer, template]
        endpoint = opening(template, recursive, 3) if source else initializer
        hypothesis = [[counter, initializer, template], endpoint]
    else:
        goal = opening(*goal, template, 2)
        hypothesis = goal

    # Compute both endpoints at the OLD floor. The compact tuple evaluates
    # the source endpoint before its Boolean index; preserve that order.
    source_endpoint = opening(template, source)
    expected_major = [source, initializer] if source else [template] * 3
    target_endpoint = opening(template, initializer)
    selected_goal = (
        source_endpoint if (major, goal) == (expected_major, target_endpoint)
        else goal
    )

    floor -= 1
    next_goal = opening(selected_goal, [floor])
    image = floor if major or 3 % len(goal) else 0
    next_hypothesis = opening(hypothesis, image)
    check(next_goal, context + (next_hypothesis,), floor)


instructions = json.load(open(0))
if type(instructions) is not list or not integer_list_tree(instructions):
    raise ValueError("Expected a JSON array of exact integers and arrays")
goal = instructions.pop()
if not public_formula(goal):
    raise ValueError("Expected a canonical closed guarded public formula")
check(goal)
print("ACCEPT")
