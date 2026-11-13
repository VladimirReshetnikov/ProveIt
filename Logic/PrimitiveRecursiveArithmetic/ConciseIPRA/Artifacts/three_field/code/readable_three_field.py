"""Readable standalone expansion of the global three-field token checker.

This is explanatory source, not a record-size contender. The interface is
the same compact finite integer/list, canonical guarded-public-goal contract.
No public grammar validator is added here; checker_native.py supplies a
different, fully validated native interface and consumes four-field packets.
"""
from json import load

scope_floor = 0


def opening(tree, image=0j, depth=0):
    try:
        return [opening(child, image, depth + 5 - len(tree)) for child in tree]
    except:
        if scope_floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)


def check(goal, *context):
    global scope_floor
    while opening(goal) not in context:
        source, seed, template = packet = next_instruction()

        # An endpoint match determines its required major. Keep the source
        # unchanged until after computing the corresponding minor premise.
        if opening(template, seed) == goal:
            goal = opening(template, source)
            source = packet[:2] if source else [template] * 3
            seed = 0

        if seed:
            counter = source and [source]
            right = opening(template, packet, 3) if source else seed
            hypothesis = [[counter, seed, template], right]
        elif source:
            check(source, *context)
            hypothesis = source * 3
        else:
            goal = opening(*goal, template, 2)
            hypothesis = goal

        scope_floor -= 1
        image = (source or len(goal) == 2) and scope_floor
        context += (opening(hypothesis, image),)
        goal = opening(goal, [scope_floor])


next_instruction = load(open(0)).pop
check(next_instruction())
print("ACCEPT")
