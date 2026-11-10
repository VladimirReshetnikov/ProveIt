"""Readable implementation of the exact compact checker protocol.

This explanatory program uses the same accepted JSON data aliases. It adds
no external oracle and is not imported by the measured compact program.
"""
from json import load

floor = 0


def open_tree(tree, image=None, depth=0):
    if isinstance(tree, list):
        increment = (32, 2, 1, 4)[len(tree)]
        return [open_tree(child, image, depth + increment) for child in tree]
    if floor <= tree < depth:
        return tree
    return open_tree(image, depth=1) if depth % 2 else 0


def check(goal, assumptions):
    global floor
    if open_tree(goal) in assumptions:
        return
    major, source, target_or_mode, motive_or_witness = pop()
    if major:
        check(major, assumptions)
        equality_request = [source, target_or_mode]
        closure_request = not source and [motive_or_witness]
        if major in (equality_request, closure_request):
            if open_tree(motive_or_witness, target_or_mode) == goal:
                goal = open_tree(motive_or_witness, source)
        new_assumption = major[2:]
    elif motive_or_witness:
        goal = open_tree(goal[2], motive_or_witness, 2)
        new_assumption = goal
    else:
        predecessor, seed, update = source
        # The source constructor is built here, so every step source has
        # exactly one successor wrapper; no submitted wrapper is trusted.
        counter = [predecessor] if target_or_mode else target_or_mode
        lhs = [counter, seed, update]
        rhs = open_tree(update, source, 1) if target_or_mode else seed
        new_assumption = [lhs, rhs]
    floor -= 1
    image = floor if major or len(goal) % 2 == major else 0
    check(open_tree(goal, [floor]),
          assumptions + [open_tree(new_assumption, image)])


try:
    pop = load(open(0)).pop
    check(pop(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
