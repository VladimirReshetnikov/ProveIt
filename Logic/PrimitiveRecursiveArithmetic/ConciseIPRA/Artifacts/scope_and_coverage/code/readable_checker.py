"""Readable expansion of the 537-byte explicit-list iPRA checker.

This is a complete standalone checker, not a wrapper around a trusted kernel.
The sorted arity interpretation and its soundness proof are in the paper.
Acceptance requires exit status zero and the exact output ACCEPT.
"""

import json


def check(goal, context, floor=0):
    """Check one goal, with immutable premise contexts and lexical fresh names."""

    def opening(tree, image=0j, depth=0):
        if isinstance(tree, list):
            return [opening(child, image, depth + 5 - len(tree)) for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)

    if opening(goal) in context:
        return

    major, source, target_or_seed, body = take()
    check(major, context, floor)

    # A paired major exports a closure. An equation or closure can also
    # perform a matching transport/specialization of the current goal.
    matches = major in (
        [source, target_or_seed],
        not source and [body] * 3,
    )
    if matches and opening(body, target_or_seed) == goal:
        goal = opening(body, source) or goal

    if major:
        hypothesis = major * 3
    elif target_or_seed:
        recursive_term = [source, target_or_seed, body]
        value = opening(body, recursive_term, 3) if source else target_or_seed
        hypothesis = [[source and [source], target_or_seed, body], value]
    else:
        # On canonical input, this opens the existential witness and
        # retains the matrix's induction/case variable as a protected slot.
        goal = opening(*goal, body, 2)
        hypothesis = goal

    floor -= 1
    assumption_image = (major or len(goal) % 2 == target_or_seed) and floor
    check(
        opening(goal, [floor]),
        context + [opening(hypothesis, assumption_image)],
        floor,
    )


take = json.load(open(0)).pop
check(take(), [[]])
print("ACCEPT")
