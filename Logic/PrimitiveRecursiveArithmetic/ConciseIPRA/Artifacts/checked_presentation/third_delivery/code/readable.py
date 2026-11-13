"""Standalone readable expansion of the 239-token compact checker.

Input: one JSON goal, then one three-field JSON packet per consumed line.
The public goal must use the inherited canonical closed guarded Eq/D syntax;
certificate trees use exact integers and lists. This module, like the compact
profiles, is not a complete public-grammar or arbitrary-JSON validator.

The global floor is a decreasing supply of numerical parameter names. A
successful verification call reserves one new name by decrementing the floor
just before returning. Context lists remain local to their recursive branches.
"""
from json import loads

scope_floor = 0


def opening(tree, image=0j, depth=0):
    """Traverse the arity codec and open its distinguished free slot.

    At arities 1, 2, 3 the child depth increments are 4, 3, 2. Odd
    depths are numerical positions; even depths are formula positions.
    The complex default 0j is an intentionally invalid missing image.
    The broad except is retained from the measured source, rather than
    silently changing its behavior when a recursive opening fails.
    """
    try:
        return [opening(child, image, depth + 5 - len(tree)) for child in tree]
    except:
        if scope_floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)


def check(context, goal):
    global scope_floor
    source, seed, template = packet = loads(input())

    # Validate the goal before evaluating the temporary computation leaf.
    validated_goal = opening(goal)
    computation = [[source and [source], seed, template],
                   opening(template, packet, 3) if source else seed]
    if validated_goal not in (*context, computation):
        # Infer the equality or closure major from an endpoint match.
        if opening(template, seed) == goal:
            goal = opening(template, source)
            source = packet[:2] if source else [template] * 3

        # Construct the unopened hypothesis before checking the major:
        # the witness must be validated against the old numerical scope.
        hypothesis = source * 3
        if not hypothesis:
            goal = opening(*goal, template, 2)
            hypothesis = goal

        # Success returns None and reserves fresh scope. This result is
        # deliberately discarded, but the call and its side effects remain.
        check(context, source)
        if source or len(goal) == 2:
            image = scope_floor
        else:
            image = False

        # False and 0 have identical behavior under every checker operation.
        # There is no type, identity, representation, or serialization test.
        new_hypothesis = opening(hypothesis, image)
        new_goal = opening(goal, [scope_floor])
        check([*context, new_hypothesis], new_goal)

    scope_floor -= 1


check([0], loads(input()))
print('ACCEPT')
