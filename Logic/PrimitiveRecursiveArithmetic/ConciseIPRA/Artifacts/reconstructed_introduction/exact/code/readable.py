"""Explanatory expansion of checker.py. This file is not the counted kernel.

The complete measured checker imports no code from this module.
Depths count only genuine binders at meaningful term constructors.
The public grammar is Eq/D; raw auxiliary arities retain the inherited
neutral readings described in the paper.
"""
import json

floor = 0
MISSING = 0j


def opening(tree, image=MISSING, depth=0):
    if type(tree) is list:
        if floor == 0 and len(tree) not in (1, 2 + depth % 2):
            raise ValueError('invalid public constructor')
        result = []
        for index, child in enumerate(tree):
            increment = (index & 2) if depth % 2 else 5 - len(tree)
            result.append(opening(child, image, depth + increment))
        return result
    if type(tree) not in (int, bool):
        raise ValueError('active scalar is neither integer nor Boolean')
    if floor <= tree < depth and floor < (depth & (tree % 2)):
        return tree or 1
    # The image is scanned eagerly, even when the parity is zero.
    checked_image = opening(image, depth=3)
    return (depth % 2) * checked_image


def check(context, goal):
    global floor
    source, mode, template = record = take()
    checked_goal = opening(goal)
    floor -= 1
    computation = [
        [[source] if source else 1, mode, template],
        opening(template, record, 3) if source else mode,
    ]
    if checked_goal in (floor, *context, computation):
        return

    if opening(template, mode) == goal:
        goal = opening(template, source)
        source = record[:2] if source else [template] * 3

    hypothesis = source * 3
    if not hypothesis:
        # The opener's three-positional-argument bound is intentional.
        # In a canonical introduction, goal is a singleton D formula.
        goal = opening(*goal, template, 2)
        hypothesis = goal

    # A witness was checked above, before this recursive call can reserve
    # further numerical names. The continuation's eigenparameter is read
    # only after the major returns.
    check(context, source)
    progressive = bool(source or len(goal) == 2 == mode)
    hypothesis = opening(hypothesis, floor if progressive else 0)
    continuation = opening(goal, [floor])
    check(context + [hypothesis], continuation)


document = json.load(open(0))
take = document.pop
check([[]], take())
print('ACCEPT')
