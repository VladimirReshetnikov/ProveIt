"""Readable expansion of compact478; same guarded public-input contract.

Only compact478 is the measured contender. This explanatory program does not
validate the public grammar, exactly as compact478 does not.
"""
import json


def check(context, goal, floor):
    def opening(tree, image=check, depth=0):
        if tree * 0 != 0:
            return [opening(child, image, depth + 5 - len(tree)) for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)

    if opening(goal) in context:
        return True
    major, source, seed, body = next_packet()
    check(context, major, floor)
    if major:
        hypothesis = major * 3
    elif seed:
        counter = source and [source]
        right = opening(body, [source, seed, body], 3) if source else seed
        hypothesis = [[counter, seed, body], right]
    else:
        goal = opening(*goal, body, 2)
        hypothesis = goal
    fresh_mode = bool(major or 3 % len(goal))
    floor -= 1
    updated_context = context + [opening(hypothesis, floor if fresh_mode else 0)]
    source_instance = opening(body, source)
    target_instance = opening(body, seed)
    required_major = source and [source, seed] or [body] * 3
    target = source_instance if (major, goal) == (required_major, target_instance) else goal
    return [check(updated_context, opening(target, [floor]), floor)]


next_packet = json.load(open(0)).pop
check([0], *next_packet())
print('ACCEPT')
