"""Readable expansion of checker.py, for the same compact input contract.

The public goal is a canonical closed guarded Eq/D formula. All proof data
are finite trees of exact integers and lists. The last record is
[goal, 0, major, source, seed, template]; other consumed records are
[major, source, seed, template], in reverse consumption order. As in the
control, unused records are permitted. This is not a separate validator for
the promised public grammar or the exact integer/list alphabet.
"""
import json


def check(context, goal, floor, major, source, seed, template):
    def opening(tree, image=check, depth=0):
        if tree * 0 != 0:
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        # The multiplication is eager, including at an even depth. The
        # nonnumeric default image is a rejecting sentinel when visited.
        return (depth % 2) * opening(image, depth=3)

    checked_goal = opening(goal)
    endpoint = opening(template, [source, seed, template], 3) if source else seed
    computation = [[source and [source], seed, template], endpoint]
    if checked_goal in context + [computation]:
        return True

    # Every call consumes a packet, even when it will finish immediately by
    # hypothesis or computation. Argument evaluation enforces that order.
    proved = check(context, major, floor, *packet())
    hypothesis = proved * major * 3
    if not hypothesis:
        goal = opening(*goal, template, 2)
        hypothesis = goal

    # any evaluates its tuple before selecting the mode; this matches the
    # strict evaluation order of the measured program.
    progressive = any((major, 3 % len(goal)))
    floor -= 1
    hypothesis = opening(hypothesis, progressive * floor)
    next_context = context + [hypothesis]

    minor = opening(template, source)
    expected_major = [source, seed] if source else [template] * 3
    target = opening(template, seed)
    continuation = minor if (major, goal) == (expected_major, target) else goal
    continuation = opening(continuation, [floor])
    return check(next_context, continuation, floor, *packet())


packet = json.load(open(0)).pop
check([[]], *packet())
print('ACCEPT')
