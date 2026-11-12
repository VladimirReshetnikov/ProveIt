"""Standalone expansion of the protected guarded certificate checker.

Input: one JSON array, containing instructions followed by the closed goal.
Instructions are consumed right to left. An unused prefix is inert. Only
normal termination with exactly ACCEPT on standard output is acceptance.

The public formula language has equations whose two terms are iterator-headed
and D formulas whose immediate atomic matrices are I(y,0;h)=I(y,0;k).
Q closures are administrative resources. The compact checker does not enforce
this public-goal grammar; strict_checker.py includes the additional validator.
All raw D formulas admit the inherited conditional-closure reading. Atomic
progress is sound by equation induction; completeness and both composites
are claimed only for the protected public language.

This program imports only JSON parsing. Proof producers, normalization,
mathematical arguments, and regression tests are not imported or executed.
"""
from json import load


def check(goal, context=([],), floor=0):
    def opening(tree, image=None, depth=0):
        if isinstance(tree, list):
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        # Even depth is a formula padding slot. Odd depth is a numerical
        # substitution hole; its proposed image must itself be in scope.
        return depth % 2 and opening(image, depth=3)

    while opening(goal) not in context:
        major, source, initializer, template = instruction()

        # The source chooses one major-premise form. Literal zero chooses
        # conditional closure; a nonzero source chooses equational transport.
        expected = [source, initializer] if source else [template] * 3
        if major == expected and opening(template, initializer) == goal:
            goal = opening(template, source)

        check(major, context, floor)
        if major:
            # A unary D major exports its three-copy Q resource.
            # Other successful arities contribute only administrative truth.
            local = major * 3
        elif initializer:
            counter = source and [source]
            recursive = [source, initializer, template]
            endpoint = (opening(template, recursive, 3)
                        if source else initializer)
            local = [[counter, initializer, template], endpoint]
        else:
            # Exact unpacking checks that the current goal is unary D.
            # Witness opening happens before allocating its eigenparameter.
            goal = opening(*goal, template, 2)
            local = goal

        floor -= 1
        # There is one introduction rule, determined by the matrix root:
        # literal equations get progress; compound matrices get their base.
        image = floor if major or len(goal) % 2 == 0 else 0
        context += (opening(local, image),)
        goal = opening(goal, [floor])


instruction = load(open(0)).pop
check(instruction())
print('ACCEPT')
