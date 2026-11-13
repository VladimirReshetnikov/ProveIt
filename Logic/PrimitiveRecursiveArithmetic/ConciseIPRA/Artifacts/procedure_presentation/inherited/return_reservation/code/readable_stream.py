"""Standalone readable return-reservation checker.

Input: canonical closed guarded Eq/D goal, then three-field JSON packets,
one value per line. The compact interface assumes integer/list raw trees.
Success is normal termination with exactly ACCEPT and one newline.

This is an expansion of frontier_ast261.py, not an imported dependency.
"""
from json import loads

floor = 0
MISSING_IMAGE = object()


def opening(tree, image=MISSING_IMAGE, depth=0):
    """Capture-avoiding raw opening, with the current numerical scope."""
    if isinstance(tree, list):
        return [opening(child, image, depth + 5 - len(tree))
                for child in tree]
    if floor <= tree < depth:
        return tree
    return depth % 2 and opening(image, depth=3)


def check(context, goal):
    global floor
    source, target, template = packet = loads(input())
    computation = [
        [source and [source], target, template],
        opening(template, packet, 3) if source else target,
    ]
    if opening(goal) not in (*context, computation):
        # A matching instance chooses substitution / closure specialization.
        if opening(template, target) == goal:
            goal = opening(template, source)
            source = packet[:2] if source else [template] * 3

        # All supplied witness data is opened in the OLD numerical scope.
        if source:
            hypothesis = source * 3
        else:
            goal = opening(*goal, template, 2)
            hypothesis = goal

        # A successful major proof leaves a genuinely new reserved name.
        # The neutral major is checked too, and therefore reserves a name.
        fresh = check(context, source)
        image = fresh * (1 if source else len(goal) == 2)
        extended = [*context, opening(hypothesis, image)]
        check(extended, opening(goal, [fresh]))

    # The returned name is below every name previously admitted by this run.
    floor -= 1
    return floor


check([0], loads(input()))
print("ACCEPT")
