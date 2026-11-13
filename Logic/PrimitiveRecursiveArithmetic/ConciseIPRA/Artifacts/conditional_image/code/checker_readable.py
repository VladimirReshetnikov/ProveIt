"""Readable standalone expansion of the 239-token checker.

Input contract: the first JSON line is a canonical closed guarded Eq/D
formula in the unshifted sorted-arity codec; subsequent consumed lines are
three-field packets [source, target, template]. Raw trees use exact integers
and lists. This explanatory interface, like the compact one, does not
independently validate that complete public-language/alphabet contract.

Success is normal termination and exactly ACCEPT followed by one newline.
Exceptions reject. Unused trailing input is allowed. Numerical parameters
in packets follow the inherited return-reservation schedule.
"""
from json import loads

floor = 0
MISSING_IMAGE = object()


def opening(tree, image=MISSING_IMAGE, depth=0):
    """The inherited sorted-arity scope check and binder opening."""
    if isinstance(tree, list):
        return [opening(child, image, depth + 5 - len(tree))
                for child in tree]
    if floor <= tree < depth:
        return tree
    # Even depth is a discarded/dummy position; odd depth inserts an image.
    # The default object fails comparison if an actual image is required.
    return depth % 2 and opening(image, depth=3)


def check(context, goal):
    global floor
    source, target, template = packet = loads(input())
    computation = [
        [source and [source], target, template],
        opening(template, packet, 3) if source else target,
    ]
    if opening(goal) not in (*context, computation):
        if opening(template, target) == goal:
            goal = opening(template, source)
            source = packet[:2] if source else [template] * 3

        # Preparing a supplied witness must precede allocation by the major.
        if source:
            hypothesis = source * 3
        else:
            goal = opening(*goal, template, 2)
            hypothesis = goal

        # Every successful check returns None. The final decrement below
        # reserves a fresh unused name for its caller. Even the neutral
        # major 0 must be checked, so this reservation is never skipped.
        check(context, source)

        # This is the new conditional image, with the major call separated
        # for readability. The compact expression is:
        # floor if check(context,source) or source or len(goal)==2 else 0.
        # Because check returns None, the separated form is equivalent.
        image = floor if source or len(goal) == 2 else 0
        extended = [*context, opening(hypothesis, image)]
        check(extended, opening(goal, [floor]))

    # Reserve only after all proof work in this call has completed.
    floor -= 1
    # Deliberately no return statement: the compact proof uses None.


check([0], loads(input()))
print('ACCEPT')
