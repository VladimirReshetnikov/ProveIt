"""Readable standalone expansion of the 300-token checker.

This file is explanatory, not the measured size record. It does not import
another checker. It retains the same evaluation order and eager opening.
"""
import json

floor = 0
MISSING = 0j


def opening(tree, image=MISSING, depth=0):
    array = tree * 0 != 0
    if array and (floor | (len(tree) in (1, 2 + depth % 2))):
        return [opening(child, image, depth + 5 - len(tree)) for child in tree]
    if floor <= tree < depth and floor < (depth & (tree % 2)):
        return tree or 1
    # Multiplication is intentional: opening(image) is checked even when
    # the coefficient is zero. An array image then gives the neutral [].
    return (depth % 2) * opening(image, depth=3)


def check(context, goal):
    global floor
    source, mode, template = record = next_packet()
    scanned = opening(goal)
    floor -= 1
    computation = [[source and [source] or 1, mode, template],
                   opening(template, record, 3) if source else mode]
    if scanned in (floor, *context, computation):
        return
    if opening(template, mode) == goal:
        goal = opening(template, source)
        source = record[:2] if source else [template] * 3
    hypothesis = source * 3
    if not hypothesis:
        # This operation must precede the recursive major proof.
        goal = opening(*goal, template, 2)
        hypothesis = goal
    check(context, source)
    image = floor if source or len(goal) == 2 == mode else 0
    hypothesis = opening(hypothesis, image)
    continuation = opening(goal, [floor])
    check([*context, hypothesis], continuation)


document = json.load(open(0))
next_packet = str(document).strip('0123456789-[], ') or document.pop
check([[]], next_packet())
print('ACCEPT')
