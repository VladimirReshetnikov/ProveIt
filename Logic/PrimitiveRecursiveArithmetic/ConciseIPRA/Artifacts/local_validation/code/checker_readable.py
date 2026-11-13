"""Standalone readable expansion of checker_exact.py.

This file explains the measured program; it is not its size record.
Every successful call returns None. Evaluation order is significant.
"""
import json

floor = 0
MISSING = 0j


def opening(tree, image=MISSING, depth=0):
    if tree * 0 == [] and (floor | (len(tree) in (1, 2 + depth % 2))):
        children = []
        for index, child in enumerate(tree):
            increment = index & 2 if depth % 2 else 5 - len(tree)
            children.append(opening(child, image, depth + increment))
        return children
    if floor <= tree < depth and floor < (depth & (tree % 2)):
        return tree or 1
    # The image is evaluated even if the multiplier is zero.
    # This is a no-image scan: the default MISSING is restored.
    return (depth % 2) * opening(image, depth=3)


def check(context, goal):
    global floor
    source, mode, template = record = next_packet()

    # The old-scope scan must precede allocation of the next negative name.
    scanned = opening(goal)
    floor -= 1
    counter = [source] if source else 1
    left = [counter, mode, template]
    right = opening(template, record, 3) if source else mode
    computation = [left, right]
    if scanned in (floor, *context, computation):
        return

    # Infer the major from an endpoint match, but still prove that major.
    if opening(template, mode) == goal:
        goal = opening(template, source)
        source = record[:2] if source else [template] * 3

    hypothesis = source * 3
    if not hypothesis:
        # Exactly a unary goal is required by this positional call.
        # In particular witness opening occurs BEFORE the major proof.
        goal = opening(*goal, template, 2)
        hypothesis = goal

    check(context, source)
    image = (source or len(goal) == 2 == mode) and floor
    new_hypothesis = opening(hypothesis, image)
    next_goal = opening(goal, [floor])
    check([*context, new_hypothesis], next_goal)


next_packet = json.load(open(0)).pop
check([[]], next_packet())
print('ACCEPT')
