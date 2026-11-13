"""Readable expansion of the 316-token intrinsic-validation checker.

This file is explanatory and is NOT the measured kernel. It preserves the
measured program's ordering of scope scans, floor changes, recursive major
proofs, eager template-instance checks, and continuation calls. The public
goal is the last item of one JSON array; proof packets are popped from its
end. A successful process prints exactly ACCEPT followed by LF.

Boolean true is permitted as the public zero-code alias 1. Public false is
rejected. Opaque unused payload may contain other JSON values. Every scalar
that the opener traverses successfully must support bitwise OR with zero,
which for JSON-decoded data means an integer or a Boolean.
"""


def check(context, goal):
    global floor

    # The packet is consumed before the goal scan. This is not a conventional
    # "try hypotheses first" checker: even a terminal call consumes a packet.
    packet = instruction()
    source, target, template, major = packet
    scanned_goal = opening(goal)

    # The public grammar is checked at floor zero. Only after that scan is
    # the fresh floor reserved, and only then is the computation candidate
    # constructed. Recursive major proofs may decrease the floor further.
    floor -= 1
    retained_candidates = (floor, *context)
    left = [[source] if source else 1, target, template]
    right = opening(template, packet[:3], 3) if source else target
    computation_candidate = [left, right]
    if scanned_goal in (*retained_candidates, computation_candidate):
        return

    # Evaluate the first argument of the continuation, in its original order.
    # Preparing a witness precedes the recursive major proof. Keeping the
    # exact positional expansion rejects an equation in a unary-intro slot.
    hypothesis = major * 3
    if not hypothesis:
        goal = opening(*goal, template, 2)
        hypothesis = goal

    major_result = check(context, major)
    eigenparameter_mode = major_result or major or len(goal) == 2 == target
    opened_hypothesis = opening(hypothesis, eigenparameter_mode and floor)
    next_context = context + [opened_hypothesis]

    # Evaluate both potential instances eagerly. In particular, this does
    # not change to a lazy conditional when no elimination match is found.
    possible_goals = (goal, opening(template, source))
    expected_major = packet[:2] if source else [template] * 3
    target_instance = opening(template, target)
    elimination_matches = (major, goal) == (expected_major, target_instance)
    next_goal = opening(possible_goals[elimination_matches], [floor])
    check(next_context, next_goal)


floor = 0


def opening(tree, image=check, depth=0):
    # For decoded JSON, only a list has list-valued product [] with zero.
    # Null and objects fail multiplication; strings give "", not [].
    if tree * 0 == [] and (floor or len(tree) in (1, 2 + depth % 2)):
        result = []
        for index, child in enumerate(tree):
            increment = index & 2 if depth % 2 else 5 - len(tree)
            result.append(opening(child, image, depth + increment))
        return result

    # Bitwise OR forces an integer/Boolean even at exposed holes. It does
    # not rely on a public type promise or a whole-document lexical pass.
    if floor <= tree | 0 < depth and (floor or depth & tree % 2):
        return tree or 1

    # This multiplication is intentionally eager: the image is checked even
    # at even depth, when the resulting administrative formula is zero.
    return depth % 2 * opening(image, depth=3)


from json import load

instruction = load(open(0)).pop
check([[]], instruction())
print('ACCEPT')
