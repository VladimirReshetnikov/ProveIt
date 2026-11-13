"""Explanatory expansion of checker269.py; not the measured candidate.

This intentionally preserves the control's order of scope checks, packet
reads and allocation. It assumes the same raw guarded-goal contract.
"""
from json import load


def check(floor, goal, *context):
    def opening(tree, image=None, depth=0):
        try:
            return [
                opening(child, image, depth + 5 - len(tree))
                for child in tree
            ]
        except:
            # Failed traversal is the inherited scalar test. None is the
            # missing-image sentinel, so a forbidden term leaf rejects.
            return (
                tree
                if floor <= tree < depth
                else depth % 2 and opening(image, depth=3)
            )

    while opening(goal) not in context:
        source, seed, template = packet = next_packet()

        # A matching endpoint reconstructs the elimination major. The
        # subsequent recursive call still has to prove that major.
        if opening(template, seed) == goal:
            goal = opening(template, source)
            source = packet[:2] if source else [template] * 3
            seed = 0

        if seed:
            hypothesis = [
                [source and [source], seed, template],
                opening(template, packet, 3) if source else seed,
            ]
        else:
            check(floor, source, *context)
            hypothesis = source * 3
            if not hypothesis:
                goal = opening(*goal, template, 2)
                hypothesis = goal

        # Allocation must occur before opening the retained hypothesis.
        # This is exactly the floor-product replacement in checker269.py.
        floor -= 1
        image = floor * (1 if source else len(goal) == 2)
        context += (opening(hypothesis, image),)
        goal = opening(goal, [floor])


next_packet = load(open(0)).pop
check(0, next_packet(), 0)
print("ACCEPT")
