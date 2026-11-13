"""Readable transcription of checker.py, preserving its evaluation order.

Only checker.py, checker_bytes.py, and checker_structure.py are measured
small kernels.  This file is an independently usable explanatory rendering.
The native theory and the sorted array codec are inherited from the
certified-zero proposal.  The new changes concern elimination scheduling
and a non-real sentinel that no JSON input can equal.
"""

import json

floor = 0


def open_tree(tree, image=0j, depth=0):
    """Validate the scope of a tree and open its escaping numerical hole.

    At meaningful formula positions the depth is even; at numerical
    positions it is odd.  Numerical roots have depth three.  Formula
    scalar padding denotes truth, so its escaping occurrence becomes 0.
    A used missing numerical image (the complex value 0j) raises TypeError.
    """
    if isinstance(tree, list):
        child_depth = depth + 5 - len(tree)
        return [open_tree(child, image, child_depth) for child in tree]
    if floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=3)
    return 0


def check(goal, context):
    global floor
    if open_tree(goal) in context:
        return

    major, source, target, template = pop_packet()

    # A successful equality pattern has length two.  A successful Q
    # pattern has length three and a false-valued source (the zero base).
    # The second candidate is instead 1j for every true-valued source.
    # A JSON-loaded value cannot equal 1j.  Consequently a false-valued
    # major never matches either candidate, and a separate major guard
    # is unnecessary.
    q_candidate = 1j if source else [template] * 3
    if major in ([source, target], q_candidate):
        if open_tree(template, target) == goal:
            # checker.py uses `... and opened_source or goal`.  Preserve
            # its deliberate stronger obligation for a false-valued image.
            opened_source = open_tree(template, source)
            if opened_source:
                goal = opened_source

    # The new goal is computed at the old scope.  The major must still
    # be proved, even after a mismatch.  Successful check() returns None,
    # so `check(major, context) or major*3` exports exactly major*3.
    if major:
        check(major, context)
        hypothesis = major * 3
    elif target:
        counter = source and [source]
        if source:
            endpoint = open_tree(template, [source, target, template], 3)
        else:
            endpoint = target
        hypothesis = [[counter, target, template], endpoint]
    else:
        # Exact unpacking is intentional.  A unary D goal contributes
        # one positional matrix; a binary equation cannot masquerade as D.
        goal = open_tree(*goal, template, 2)
        hypothesis = goal

    floor -= 1
    successor_goal = open_tree(goal, [floor])
    hypothesis_image = floor if major or len(goal) % 2 == major else 0
    opened_hypothesis = open_tree(hypothesis, hypothesis_image)
    check(successor_goal, context + [opened_hypothesis])


pop_packet = json.load(open(0)).pop
check(pop_packet(), [])
print("ACCEPT")
