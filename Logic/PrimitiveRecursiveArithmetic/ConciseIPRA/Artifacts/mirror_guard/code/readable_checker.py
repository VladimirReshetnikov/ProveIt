"""Standalone local-scope checker for the mirrored guarded presentation.

Input is one JSON array. Its last item is the closed goal. Remaining
instruction records [major, source, initializer, template] are consumed
backwards. Success is normal exit with exactly ACCEPT followed by newline.
Exceptions reject. There are no imported proof producers or axiom files.

Canonical object formulas are equations and D formulas. An atomic matrix
under D has shape a = I(y,a;u.h), with the initializer a repeated on the
left. Q occurs as a closure resource in proof contexts. The compact core
also processes administrative aliases with the interpretations stated in
the report. Use strict_checker.py to validate canonical goal syntax first.
"""
from json import load


def check(goal, context=([],), floor=0):
    def opening(tree, image=None, depth=0):
        try:
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        except:
            return (tree if floor <= tree < depth
                    else depth % 2 and opening(image, depth=3))

    while opening(goal) not in context:
        major, source, initializer, template = instruction()

        # A nonzero source selects equality; zero selects Q elimination.
        expected = [source, initializer] if source else [template] * 3
        if major == expected and opening(template, initializer) == goal:
            goal = opening(template, source)

        check(major, context, floor)
        if major:
            # A D major exports Q at a fresh witness. Other array arities
            # export administrative truth, so there is no DE opcode.
            local = major * 3
        elif initializer:
            counter = source and [source]
            recursive = [source, initializer, template]
            endpoint = opening(template, recursive, 3) if source else initializer
            local = [[counter, initializer, template], endpoint]
        else:
            # Exact argument count admits only a unary D goal (or truth).
            goal = opening(*goal, template, 2)
            local = goal

        floor -= 1
        # Equation matrices use progress; compound matrices use cases.
        image = (major or len(goal) % 2 == 0) and floor
        context += (opening(local, image),)
        goal = opening(goal, [floor])


instruction = load(open(0)).pop
check(instruction())
print('ACCEPT')
