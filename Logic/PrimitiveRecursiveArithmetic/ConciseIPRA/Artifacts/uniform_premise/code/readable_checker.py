"""Readable expansion of checker.py; a complete independent CLI program.

The compact file does not import this file. Both implement the same inference
checks. Exceptions reject; only normal completion prints ACCEPT. A successful
trace has array-rooted goals and context entries, by the report's invariant.
"""
import json

fresh_floor = 0


def opening(expression, image=None, depth=0):
    """Open one numerical slot, validating its inserted image at root depth 3."""
    if isinstance(expression, list):
        child_depth = depth + 5 - len(expression)
        return [opening(child, image, child_depth) for child in expression]
    if fresh_floor <= expression < depth:
        return expression
    if depth % 2:
        return opening(image, depth=3)
    return 0


def prove(goal, context):
    global fresh_floor
    if opening(goal) in context:
        return

    major, source, initializer, template = next_instruction()

    # Even computation and introduction prove their explicit neutral major [].
    prove(major, context)

    equality_major = [source, initializer]
    closure_major = not source and [template] * 3
    if major in (equality_major, closure_major):
        if opening(template, initializer) == goal:
            goal = opening(template, source)

    if major:
        # Unary D exports Q; every larger array exports a truth alias.
        hypothesis = major * 3
    elif initializer:
        if source:
            counter = [source]
            recursive_value = [source, initializer, template]
            endpoint = opening(template, recursive_value, 3)
        else:
            counter = source
            endpoint = initializer
        hypothesis = [[counter, initializer, template], endpoint]
    else:
        # The exact unpacking and depth are the same as in the measured file.
        goal = opening(*goal, template, 2)
        hypothesis = goal

    fresh_floor -= 1
    retain_arbitrary_instance = major or len(goal) % 2 == initializer
    hypothesis_image = retain_arbitrary_instance and fresh_floor
    prove(opening(goal, [fresh_floor]),
          context + [opening(hypothesis, hypothesis_image)])


next_instruction = json.load(open(0)).pop
prove(next_instruction(), [[]])
print('ACCEPT')
