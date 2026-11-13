"""Readable expansion of the strict three-field checker.

This is explanatory source, not a size contender. The compact implementation
uses the same initial validation, source dispatch, openings and local floors.
Public numeric zero is encoded by 1. The integer 0 remains a control value.
"""
import json

MISSING = object()


def check(context, goal, floor=0):
    def opening(tree, image=MISSING, depth=0):
        if isinstance(tree, list):
            if not context and len(tree) not in (1, 2 + depth % 2):
                raise ValueError("Invalid public arity")
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if not isinstance(tree, int):
            raise ValueError("Missing image or invalid scalar")
        if floor <= tree < depth and (context or depth & (tree % 2)):
            return tree or 1
        if depth % 2 or not context:
            return opening(image, depth=3)
        return 0

    if opening(goal) in context:
        return

    # This neutral resource also ends the one-time public-grammar phase.
    context += [0]
    source, seed, template = record = next_record()

    # Select ordinary equality transport or closure specialization.
    if opening(template, seed) == goal:
        goal = opening(template, source)
        source = record[:2] if source else [template] * 3
        seed = 0

    if seed:
        counter = source and [source]
        rhs = opening(template, record, 3) if source else seed
        hypothesis = [[counter, seed, template], rhs]
    else:
        # The major is proved before its closure becomes available.
        check(context, source, floor)
        if source:
            hypothesis = source * 3
        else:
            goal = opening(*goal, template, 2)
            hypothesis = goal

    floor -= 1
    image = floor if source or len(goal) % 2 == seed else 0
    check(context + [opening(hypothesis, image)],
          opening(goal, [floor]), floor)


packet_stack = json.load(open(0))
# This gate rejects every non-list/non-integer value anywhere in the input,
# including ignored data; bool is not an allowed public JSON scalar.
if str(packet_stack).strip('0123456789-[], '):
    raise ValueError("Only integer/list JSON is admitted")
next_record = packet_stack.pop
check([], next_record())
print("ACCEPT")
