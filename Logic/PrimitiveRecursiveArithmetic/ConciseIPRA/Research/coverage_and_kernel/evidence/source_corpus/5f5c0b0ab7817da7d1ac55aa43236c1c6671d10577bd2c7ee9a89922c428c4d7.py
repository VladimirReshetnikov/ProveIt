"""Readable reference for atomic.py's exact proof protocol.

This program is an explanatory reference, not the measured compact kernel.
It retains the source kernel's JSON parser and permissive inert aliases.
Only successful checking traces are mathematically significant.
"""
from json import load


class Rejection(Exception):
    """An explicit false computation comparison."""


floor = 0


def open_tree(tree, image=None, depth=0):
    """Validate and open exposed slots using the inherited sorted decoder."""
    if isinstance(tree, list):
        increment = (32, 2, 1, 4)[len(tree)]
        return [open_tree(child, image, depth + increment) for child in tree]
    if floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=1)
    return 0


def check(goal, context):
    global floor
    major, source, target, motive = pop()

    if major:
        # Availability is legal only at an elimination-major edge.
        if open_tree(major) not in context:
            check(major, context)

        # len(motive) is intentionally evaluated for every major instruction,
        # including DE; canonical DE packets therefore set motive = [].
        candidate_equation = len(motive) == 2 and [source, target]
        candidate_closure = not source and [motive]
        if major in (candidate_equation, candidate_closure):
            if open_tree(motive, target) == goal:
                check(open_tree(motive, source), context)
                return

        # An unmatched unary/binary major raises here; it cannot masquerade
        # as a paired-elimination instruction.
        hypothesis = [major[2]]

    elif motive:
        # The numerical witness occupies the packet's motive field.
        # The remaining closure coordinate is protected at depth 2.
        goal = open_tree(goal[2], motive, 2)
        hypothesis = goal

    else:
        # R(0,a;u,v.h) = S(a),
        # R(S(n),a;u,v.h) = h[n/u, R(n,a;u,v.h)/v].
        (counter, seed, update), actual = goal
        if counter:
            predecessor, = counter
            counter_opened = open_tree(update, predecessor, 3)
            recursive_state = [predecessor, seed, update]
            expected = open_tree(counter_opened, recursive_state, 1)
        else:
            expected = [seed]
        if actual != expected:
            raise Rejection("computation endpoints differ")
        return

    # Scope validation has preceded allocation. A new rigid coordinate is
    # absent from every retained numerical parameter and from the witness.
    floor -= 1
    step_goal = open_tree(goal, [floor])
    if major or len(goal) % 2 == major:
        hypothesis_image = floor
    else:
        hypothesis_image = 0
    opened_hypothesis = open_tree(hypothesis, hypothesis_image)
    check(step_goal, context + [opened_hypothesis])


try:
    pop = load(open(0)).pop
    check(open_tree(pop()), [])
except:
    print("REJECT")
    raise
print("ACCEPT")
