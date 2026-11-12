"""Standalone expansion of the local 521-byte proof-checker profile.

The public contract is a canonical closed guarded Eq/D goal. This program
checks its proof but, like the compact profiles, does not separately validate
that public grammar. checker_strict.py supplies that additional validator.
Instructions are four-field JSON arrays consumed from right to left. A
neutral major is the scalar 0, not the earlier empty array. An unused prefix
is permitted. Acceptance requires normal exit and exactly ACCEPT followed
by a newline. Exceptions reject. The only imported dependency is json.

Raw intermediate arrays retain the inherited sorted administrative meaning.
In particular a raw Q resource is ternary, and an unguarded atomic D is a
progressive auxiliary formula. No interpretation claim for arbitrary raw
public goals is made here.
"""
import json


def check(goal, context=(0,), floor=0):
    def opening(tree, image=0j, depth=0):
        if isinstance(tree, list):
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        # At a formula position, scalar padding is truth. At a numerical
        # position, an actual image is checked before filling a free hole.
        return depth % 2 and opening(image, depth=3)

    if opening(goal) in context:
        return

    major, source, initializer, template = instruction()

    # Source-selected elimination. Literal zero selects Q elimination;
    # other sources select equality transport. The major is checked below.
    expected_major = [source, initializer] if source else [template] * 3
    if major == expected_major and opening(template, initializer) == goal:
        replacement = opening(template, source)
        if replacement:
            goal = replacement

    check(major, context, floor)
    if major:
        # D exports its Q resource; other array arities export padding truth.
        hypothesis = major * 3
    elif initializer:
        # The initializer and successor predecessor restrictions in compact
        # packets are discharged by the inherited certified-zero expansion.
        counter = source and [source]
        recursive = [source, initializer, template]
        endpoint = opening(template, recursive, 3) if source else initializer
        hypothesis = [[counter, initializer, template], endpoint]
    else:
        # Unpacking requires a unary D goal; open its witness first.
        goal = opening(*goal, template, 2)
        hypothesis = goal

    floor -= 1
    # An atomic matrix receives its progress hypothesis. Compound matrices
    # receive their zero instance. A genuine major exports at a fresh name.
    image = floor if major or len(goal) == 2 else 0
    next_goal = opening(goal, [floor])
    next_hypothesis = opening(hypothesis, image)
    check(next_goal, context + (next_hypothesis,), floor)


instruction = json.load(open(0)).pop
check(instruction())
print('ACCEPT')
