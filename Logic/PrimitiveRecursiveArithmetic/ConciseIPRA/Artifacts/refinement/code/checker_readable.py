"""Readable standalone expansion of the 488-byte compact checker.

The public contract is the same compact guarded calculus contract. This
module deliberately does not import its compact counterpart. The order of
scope changes, scope checks, and proof-stream reads is part of the algorithm.
"""
import json


def check(context, goal, floor=0):
    """Return True or a nested singleton list after a finite successful check."""

    def opening(tree, image=check, depth=0):
        # The function object used as the default is a rejection sentinel.
        if tree * 0 != 0:
            return [opening(child, image, depth + 5 - len(tree)) for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)

    # This scope scan must precede the hypothesis membership test.
    if opening(goal) in context:
        return True

    major, source, seed, template = next_packet()

    # Check the major before considering any other instruction payload.
    major_success = check(context, major, floor)
    raw_hypothesis = major_success and major * 3
    if not raw_hypothesis:
        raw_hypothesis = seed and [
            [source and [source], seed, template],
            opening(template, [source, seed, template], 3) if source else seed,
        ]
    if not raw_hypothesis:
        goal = opening(*goal, template, 2)
        raw_hypothesis = goal

    # Mode selection precedes allocation, but hypothesis opening follows it.
    progressive_or_major = bool(major or 3 % len(goal))
    floor = ~-floor
    retained_hypothesis = opening(raw_hypothesis, progressive_or_major * floor)
    extended_context = context + [retained_hypothesis]

    # Selection is eager. In particular, the source opening is computed even
    # when the major/target pair will not match an elimination instruction.
    source_instance = opening(template, source)
    inferred_major = source and [source, seed] or [template] * 3
    target_instance = opening(template, seed)
    is_elimination = (major, goal) == (inferred_major, target_instance)
    continuation_goal = (goal, source_instance)[is_elimination]
    continuation_goal = opening(continuation_goal, [floor])

    # A list is eager; merely creating a generator here would be unsound.
    return [check(extended_context, continuation_goal, floor)]


next_packet = json.load(open(0)).pop
check([0], next_packet())
print('ACCEPT')
