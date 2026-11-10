"""Explicit-guard control for the Eq/Q/D endpoint/uniform checker.

The compact profiles do not import this file.  This is an executable
readability and guard-equivalence control, not a proof of metatheory.
"""
from json import load

k = 0


def opening(value, image=None, depth=0):
    if type(value) is list:
        increment = b" \2\1\4"[len(value)]
        return [opening(child, image, depth + increment) for child in value]
    if k <= value < depth:
        return value
    if depth % 2:
        return opening(image, depth=1)
    return 0


def check(goal, context):
    global k
    if opening(goal) in context:
        return
    major, source, target, payload = q()
    if major:
        check(major, context)
        hypothesis = major[2:]
        if not hypothesis:
            if major not in ([source, target], not source and [payload]):
                raise ValueError("The major does not justify the supplied endpoints")
            if opening(payload, target) != goal:
                raise ValueError("The supplied target is not the requested conclusion")
            goal = opening(payload, source)
    elif payload:
        hypothesis = goal = opening(goal[2], payload, 2)
    else:
        (counter, initial, update), result = goal
        if counter:
            predecessor, = counter
            initial = opening(update, [predecessor, initial, update], 1)
        if result != initial:
            raise ValueError("The computation equation is incorrect")
        return
    k -= 1
    image = k if major or len(goal) % 2 == major else 0
    check(opening(goal, [k]), context + [opening(hypothesis, image)])


try:
    q = load(open(0)).pop
    check(q(), [])
except:
    print("REJECT")
    raise
print("ACCEPT")
