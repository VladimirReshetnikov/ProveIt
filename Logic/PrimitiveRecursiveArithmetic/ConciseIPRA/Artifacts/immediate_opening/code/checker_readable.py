"""Readable expansion of checker479, with the same compact input contract.

Only the compact module is the source-size record. This explanatory module
keeps the scope scan, eager template evaluations, and old/new floor phases.
Input is one possibly multiline JSON certificate, consumed from its end.
"""

import json


def check(context, goal, floor=0):
    """Return True or a nonempty list after a finite successful check."""

    def open_tree(tree, image=check, depth=0):
        """The affine opener; with no image it also checks numerical scope.

        The function-valued default is an error sentinel, not a numeral.
        The closure intentionally reads the current value of ``floor``:
        a transition lowers that value between constructing and opening
        its new resource.
        """
        if tree * 0 != 0:
            return [
                open_tree(child, image, depth + 5 - len(tree))
                for child in tree
            ]
        if floor <= tree < depth:
            return tree
        return depth % 2 and open_tree(image, depth=3)

    # This full traversal must precede membership, even for a retained goal.
    if open_tree(goal) in context:
        return True

    major, source, seed, template = next_packet()

    # The original expression checks the major even when it is the neutral
    # scalar 0. That scalar is retained in every context.
    major_result = check(context, major, floor)
    resource = major_result and major * 3
    if not resource:
        resource = seed and [
            [source and [source], seed, template],
            open_tree(template, [source, seed, template], 3) if source else seed,
        ]
    if not resource:
        goal = open_tree(*goal, template, 2)
        resource = goal

    # All resource construction above used the old numerical scope.
    selector = bool(major or 3 % len(goal))
    floor = floor - 1
    opened_resource = open_tree(resource, selector * floor)
    next_context = context + [opened_resource]

    # Both the tuple of alternatives and the comparison tuple are evaluated
    # eagerly in checker479, in this order. A conditional expression here
    # would skip a scope traversal and would not be the same protocol.
    alternatives = (goal, open_tree(template, source))
    matches = (major, goal) == (
        source and [source, seed] or [template] * 3,
        open_tree(template, seed),
    )
    next_goal = open_tree(alternatives[matches], [floor])

    # The singleton list preserves the compact checker's truth-valued return.
    return [check(next_context, next_goal, floor)]


next_packet = json.load(open(0)).pop
check([0], next_packet())
print("ACCEPT")
