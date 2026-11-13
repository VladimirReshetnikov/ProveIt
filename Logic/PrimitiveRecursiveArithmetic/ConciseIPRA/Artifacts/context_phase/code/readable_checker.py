"""Readable implementation of the context-phase checker.

The measured standalone acceptance program is checker.py. This expansion
keeps its operation order and uses immutable contexts. It accepts the same
JSON certificates, subject to ordinary finite Python resource limits.
"""

import json
import sys


def check(goal, context=(), floor=0):
    def opening(tree, image=check, depth=0):
        public_phase = not context
        if isinstance(tree, list) and (
            not public_phase or len(tree) in (1, 2 + depth % 2)
        ):
            return [
                opening(child, image, depth + 5 - len(tree)) for child in tree
            ]
        if floor <= tree < depth and (
            not public_phase
            or (
                int(tree) is tree
                and depth % 2
                and (not tree or tree > 1 == tree % 2)
            )
        ):
            return tree
        if depth % 2 or public_phase:
            return opening(image, depth=3)
        # Scalar padding in an internal formula position is neutral truth.
        return False

    if opening(goal) in context:
        return

    # The root context was empty. From now on every context contains truth.
    # Repeated copies are harmless and avoid an extra phase flag or branch.
    context += (0,)
    major, source, initializer, template = instruction()
    check(major, context, floor)

    if major:
        hypothesis = major * 3
    elif initializer:
        successor_counter = source and [source]
        recursive_term = [source, initializer, template]
        endpoint = opening(template, recursive_term, 3) if source else initializer
        hypothesis = [[successor_counter, initializer, template], endpoint]
    else:
        goal = opening(*goal, template, 2)
        hypothesis = goal

    expected_major = [source, initializer] if source else [template] * 3
    if major == expected_major and opening(template, initializer) == goal:
        rewritten_goal = opening(template, source) or goal
    else:
        rewritten_goal = goal

    # Evaluate the possible rewrite at the old floor, then allocate the
    # fresh eigenparameter before opening either continuation argument.
    floor -= 1
    next_goal = opening(rewritten_goal, [floor])
    image = (major or len(goal) % 2 == initializer) and floor
    next_hypothesis = opening(hypothesis, image)
    check(next_goal, context + (next_hypothesis,), floor)


instruction = json.load(sys.stdin).pop
check(instruction())
print("ACCEPT")
