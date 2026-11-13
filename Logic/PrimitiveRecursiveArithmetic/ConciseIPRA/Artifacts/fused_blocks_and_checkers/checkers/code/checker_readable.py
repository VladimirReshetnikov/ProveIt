"""Readable standalone form of the 239-token certificate checker.

Input: a canonical closed guarded Eq/D goal on the first JSON line, followed
by three-field proof packets, one per line. Raw data has exact integers and
lists. This file is explanatory; the compact checkers do not import it.

Successful termination prints ACCEPT. Any exception rejects. Every proof
call reserves one fresh numerical name when it successfully returns.
"""
from json import loads

scope_floor = 0
MISSING_IMAGE = 0j


def opening(tree, image=MISSING_IMAGE, depth=0):
    """The inherited sorted-arity opening, with the lower scope bound intact."""
    if isinstance(tree, list):
        return [opening(child, image, depth + 5 - len(tree))
                for child in tree]
    if scope_floor <= tree < depth:
        return tree
    return depth % 2 and opening(image, depth=3)


def check(context, goal):
    global scope_floor
    source, target, template = packet = loads(input())
    computation = [
        [source and [source], target, template],
        opening(template, packet, 3) if source else target,
    ]
    if opening(goal) not in (*context, computation):
        if opening(template, target) == goal:
            goal = opening(template, source)
            source = packet[:2] if source else [template] * 3

        # Witness preparation remains in the old numerical scope.
        if source:
            prepared_hypothesis = source * 3
        else:
            goal = opening(*goal, template, 2)
            prepared_hypothesis = goal

        # This also executes for the administrative neutral major zero.
        check(context, source)
        if source or len(goal) == 2:
            image = scope_floor
        else:
            image = False
        extended = [*context, opening(prepared_hypothesis, image)]
        check(extended, opening(goal, [scope_floor]))

    scope_floor -= 1


check([0], loads(input()))
print("ACCEPT")
