"""Readable expansion of checker_bytes460.py under its stated contract.

The input is an integer/list JSON certificate stack. Its final row is
[closed_public_goal, 0]. Instruction rows are [source, target, template,
major]. The public goal uses the inherited guarded Eq/D language; auxiliary
internal trees have the inherited sorted arity reading. This is an
explanatory reference implementation, not one of the measured minima.

No normalization or proof search is performed. One certificate record is
consumed at every verification call, including hypothesis leaves.
"""

import json
import sys


MISSING = object()


def verify(context, goal, floor, read_record):
    source, target, template, major = read_record()

    def opening(tree, image=MISSING, depth=2):
        if isinstance(tree, list):
            child_depth = depth + 5 - len(tree)
            return [opening(child, image, child_depth) for child in tree]
        if type(tree) is not int:
            raise ValueError("The opening operation has no numerical image")
        if floor <= tree < depth:
            return tree
        # Eager image validation is intentional, including at even depth.
        validated_image = opening(image, depth=5)
        return (depth % 2) * validated_image

    checked_goal = opening(goal)
    counter = [source] if source else source
    image = [source, target, template]
    result = opening(template, image, 5) if source else target
    computation_equation = [[counter, target, template], result]
    if checked_goal in context + [computation_equation]:
        return

    # Major proof first. A successful call is a procedure and returns None.
    verify(context, major, floor, read_record)
    if major:
        raw_resource = major * 3
    else:
        # Preserve the literal raw protocol, including Python's unpacking
        # arity checks. On canonical syntax goal is a one-element D tree.
        goal = opening(*goal, template, 4)
        raw_resource = goal

    # Only a unary major exports a substantive witness assumption.
    # With no major, tail parity selects progress only for an equation.
    progressive_or_opening = len(major or goal[1:]) % 2
    floor -= 1
    resource = opening(raw_resource, floor if progressive_or_opening else 0)

    # Both alternatives and the endpoint are evaluated in the compact code.
    predecessor_goal = opening(template, source)
    expected_major = [source, target] if source else [template] * 3
    expected_endpoint = opening(template, target)
    if (major, goal) == (expected_major, expected_endpoint):
        goal = predecessor_goal
    minor_goal = opening(goal, [floor])
    verify(context + [resource], minor_goal, floor, read_record)


def main():
    stack = json.load(sys.stdin)
    goal, floor = stack.pop()
    verify([0], goal, floor, stack.pop)
    print("ACCEPT")


if __name__ == "__main__":
    main()

