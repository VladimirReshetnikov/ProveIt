"""Readable implementation of offset472.py on its integer/list contract.

The mathematical target and compact input contract are stated in
OFFSET_PROOF.txt. This implementation makes the evaluation order explicit;
it is not the module used for the 472-byte measurement.
"""
import json


MISSING = object()


def check(context, goal, floor):
    def opening(tree, image=MISSING, depth=2):
        if type(tree) is list:
            child_depth = depth + 5 - len(tree)
            return [opening(child, image, child_depth) for child in tree]
        if type(tree) is not int:
            raise TypeError('A visited scalar is not an exact integer')
        if floor <= tree < depth:
            return tree
        # Evaluate the image even at even depth, as in the compact program.
        checked_image = opening(image, depth=5)
        return (depth % 2) * checked_image

    checked_goal = opening(goal)
    if checked_goal in context:
        return True

    major, source, target, template = take_packet()

    computation_left = [source and [source], target, template]
    computation_right = (
        opening(template, [source, target, template], 5)
        if source else target
    )
    if goal == [computation_left, computation_right]:
        return True

    # This recursive check is mandatory even for the scalar neutral major0.
    check(context, major, floor)
    hypothesis = major * 3
    if not hypothesis:
        # Genuine D goals are unary; the empty-array truth alias may also
        # enter this raw call. Preserve the compact argument-splicing exactly.
        goal = opening(*goal, template, 4)
        hypothesis = goal

    # The second argument to any is evaluated even when major is truthy.
    progressive = any((major, 3 % len(goal)))
    floor -= 1
    hypothesis = opening(hypothesis, progressive * floor)
    extended_context = context + [hypothesis]

    # Both alternatives are evaluated before selection in offset472.py.
    minor = opening(template, source)
    expected_major = [source, target] if source else [template] * 3
    expected_goal = opening(template, target)
    selected = minor if (major, goal) == (expected_major, expected_goal) else goal
    continuation_goal = opening(selected, [floor])
    check(extended_context, continuation_goal, floor)
    return True


take_packet = json.load(open(0)).pop
check([0], *take_packet())
print('ACCEPT')
