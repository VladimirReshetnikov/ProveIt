"""Readable retained-major checker, equivalent to retained_bytes.py.

Contract: canonical closed guarded Eq/D public goals, with integer/list
certificate trees. Instructions are four-field arrays consumed from right
to left. An unused prefix is permitted. Acceptance is normal exit and exactly
ACCEPT followed by LF. This expansion does not add a public grammar validator.

The compact arity codec and its scope traversal are inherited. The new rule
uses an already retained equality or closure as its major premise, checks its
minor premise recursively, and retains the resulting conclusion for subsequent
instructions. The remaining instruction branch is inherited unchanged.
"""
import json


POISON = object()


def opening(tree, image=POISON, depth=0, floor=0):
    """Open the distinguished hole, checking all numerical scopes en route."""
    if tree * 0 != 0:
        return [opening(child, image, depth + 5 - len(tree), floor)
                for child in tree]
    if floor <= tree < depth:
        return tree
    return depth % 2 and opening(image, depth=3, floor=floor)


def check(goal, context=(0,), floor=0):
    if opening(goal, floor=floor) in context:
        return
    major, source, target, template = instruction()
    expected = [source, target] if source else [template] * 3

    if expected in context:
        # Equality: F(source) -> F(target), using source = target in context.
        # Closure: B(0) -> B(target), using Q_y B(y) in context.
        minor = opening(template, source, floor=floor)
        check(minor, context, floor)
        hypothesis = opening(template, target, floor=floor)
    else:
        check(major, context, floor)
        if major:
            # A D major opens its conditional closure at a fresh parameter.
            # Other major arities contribute administrative padding.
            hypothesis = major * 3
        elif target:
            # The two inherited computation packets. The zero/successor
            # source restrictions are handled by their certified encodings.
            recursive_term = [source, target, template]
            endpoint = opening(template, recursive_term, 3, floor) if source else target
            hypothesis = [[source and [source], target, template], endpoint]
        else:
            # Introduce a D goal. Its matrix determines progress versus cases.
            goal = opening(*goal, template, 2, floor)
            hypothesis = goal

    floor -= 1
    fresh_image = floor if major or ~len(goal) % 2 else 0
    next_goal = opening(goal, [floor], floor=floor)
    next_hypothesis = opening(hypothesis, fresh_image, floor=floor)
    check(next_goal, context + (next_hypothesis,), floor)


instruction = json.load(open(0)).pop
check(instruction())
print('ACCEPT')
