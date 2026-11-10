"""Readable expansion of the neutral-major, lexical-scope checker.

This is a standalone executable explanatory implementation. It does not import
any compact checker. The public certificate is data; no Python is evaluated.
The empty list is a canonical truth formula. Lists in contexts are never
mutated; every continuation receives a fresh list. All numerical and logical
operations performed by the compact kernel are displayed below.
"""

import json


def check(goal, context=None, floor=0):
    if context is None:
        context = [[]]

    def opening(expression, replacement=0j, depth=0):
        if isinstance(expression, list):
            child_depth = depth + 5 - len(expression)
            return [opening(child, replacement, child_depth)
                    for child in expression]
        if floor <= expression < depth:
            return expression
        if depth % 2:
            return opening(replacement, depth=3)
        return 0

    if opening(goal) in context:
        return

    major, source, initializer_or_mode, template = next_packet()
    target = initializer_or_mode
    check(major, context, floor)

    major_matches = major in (
        [source, target],
        not source and [template] * 3,
    )
    if major_matches and opening(template, target) == goal:
        previous_goal = opening(template, source)
        if previous_goal:
            goal = previous_goal

    generated_hypothesis = major * 3
    if not generated_hypothesis:
        if initializer_or_mode:
            counter = source and [source]
            recursive_call = [source, initializer_or_mode, template]
            if source:
                result = opening(template, recursive_call, 3)
            else:
                result = initializer_or_mode
            generated_hypothesis = [
                [counter, initializer_or_mode, template], result
            ]
        else:
            goal = opening(*goal, template, 2)
            generated_hypothesis = goal

    floor -= 1
    needs_fresh_image = major or len(goal) % 2 == initializer_or_mode
    assumption_image = needs_fresh_image and floor
    new_goal = opening(goal, [floor])
    new_hypothesis = opening(generated_hypothesis, assumption_image)
    check(new_goal, context + [new_hypothesis], floor)


next_packet = json.load(open(0)).pop
check(next_packet())
print('ACCEPT')
