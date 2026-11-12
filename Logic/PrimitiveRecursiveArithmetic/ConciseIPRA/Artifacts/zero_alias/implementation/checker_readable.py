"""Readable standalone checker for the public zero-alias presentation.

This file imports only json.  Exact integer/list validation includes unused
certificate prefixes.  The public root has native Eq/D arities, odd numerical
coordinates, and no free negative coordinates.  Canonical semantic encodings
do not refer to the arithmetic constructors' artificial binder slots.
"""
import json


def exact_alphabet(value):
    if type(value) is int:
        return
    if type(value) is not list:
        raise ValueError('Only exact integers and lists are admitted')
    for child in value:
        exact_alphabet(child)


def check(context, goal, floor=0, public=False):
    def opening(tree, image=check, depth=0):
        if type(tree) not in (int, list):
            raise ValueError('Missing substitution image')
        if (type(tree) is list and
                (not public or len(tree) in (1, 2 + depth % 2))):
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if (type(tree) is int and floor <= tree < depth and
                (not public or depth % 2 & tree)):
            return tree
        if depth % 2 or public:
            return opening(image, depth=3)
        return 0

    if opening(goal) in context:
        return
    major, source, target, template = packets.pop()
    public = False
    check(context, major, floor)
    if major:
        hypothesis = major * 3
    elif target:
        counter = [source] if source else source
        predecessor_iterator = [source, target, template]
        rhs = (opening(template, predecessor_iterator, 3)
               if source else target)
        hypothesis = [[counter, target, template], rhs]
    else:
        goal = opening(*goal, template, 2)
        hypothesis = goal
    progressive = bool(major or len(goal) % 2 == target)
    floor -= 1
    hypothesis = opening(hypothesis, floor if progressive else 0)
    # Preserve the compact checker's eager traversal order.
    source_instance = opening(template, source)
    required_major = [source, target] if source else [template] * 3
    target_instance = opening(template, target)
    selected = (source_instance if (major, goal) ==
                (required_major, target_instance) else goal)
    goal = opening(selected, [floor])
    check(context + [hypothesis], goal, floor)


packets = json.load(open(0))
exact_alphabet(packets)
check([0, [1, 0]], packets.pop(), public=True)
print('ACCEPT')
