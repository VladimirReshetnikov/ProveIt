"""Readable standalone expansion of checker468.py.

Contract: a JSON array of four-field packets, followed by [goal, 0].
The public goal is a canonical closed guarded Eq/D formula; numerical and
formula trees in the compact interface contain exact integers and lists.
Packets are consumed from right to left. Exceptions reject. Acceptance is
normal exit and exactly ACCEPT followed by LF. An unused prefix is allowed.

This expansion deliberately keeps the compact checker's scope schedule,
eager numerical-image validation, administrative arrays and leaf protocol.
It is explanatory source; its larger size is measured separately.
"""
import json

MISSING = object()


def check(context, goal, floor):
    def opening(tree, image=MISSING, depth=2):
        if tree * 0 != 0:
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        # Even-depth multiplication still validates the image eagerly.
        return depth % 2 * opening(image, depth=5)

    major, source, seed, template = next_packet()
    validated_goal = opening(goal)
    recursive_term = [source, seed, template]
    computation = [
        [source and [source], seed, template],
        opening(template, recursive_term, 5) if source else seed,
    ]
    if validated_goal in context + [computation]:
        return True

    # Every non-leaf checks its major in the old context and old scope.
    check(context, major, floor)
    hypothesis = major * 3
    if not hypothesis:
        goal = opening(*goal, template, 4)
        hypothesis = goal

    # The image selector precedes allocation, as in the compact expression.
    progressive = any((major, 3 % len(goal)))
    floor -= 1
    hypothesis = opening(hypothesis, progressive * floor)

    # Both candidate minor and target instances are opened in the NEW scope.
    # Their order is deliberate: tuple selection in the compact source is eager.
    minor = opening(template, source)
    required_major = [source, seed] if source else [template] * 3
    target = opening(template, seed)
    if (major, goal) == (required_major, target):
        goal = minor
    goal = opening(goal, [floor])
    return check(context + [hypothesis], goal, floor)


next_packet = json.load(open(0)).pop
check([0], *next_packet())
print('ACCEPT')
