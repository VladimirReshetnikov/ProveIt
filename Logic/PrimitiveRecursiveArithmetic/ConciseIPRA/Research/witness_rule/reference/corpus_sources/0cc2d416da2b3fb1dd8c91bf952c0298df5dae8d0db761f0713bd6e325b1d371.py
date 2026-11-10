"""Choice-DI/iPRA checker with a persistent context and iterative continuations.

This is an explanatory implementation of loop_tuple_try.py.  The packet
language and primitive theory are inherited from the flat-computation draft.
Only the standard JSON parser is imported; no numerical evaluator is used.
"""
from json import load

floor = 0


def open_tree(tree, image=None, depth=0):
    """Validate/open raw syntax; successful aliases follow the inherited codec."""
    try:
        increment = (32, 2, 1, 4)[len(tree)]
        return [open_tree(child, image, depth + increment) for child in tree]
    except Exception:
        if floor <= tree < depth:
            return tree
        return depth % 2 and open_tree(image, depth=1)


def check(goal, context):
    global floor
    while open_tree(goal) not in context:
        major, source, target, template = read_instruction()
        if major:
            # The recursive call cannot change this immutable tuple context.
            check(major, context)
            if (major in ([source, target], not source and [template])
                    and open_tree(template, target) == goal):
                goal = open_tree(template, source)
            hypothesis = major[2:]
        elif major is None:
            # Counter, seed and update are the three flat packet fields.
            # list(*source) eagerly enforces the successor constructor shape.
            recursive = ([list(*source), target, template] if source else None)
            result = open_tree(template, recursive, 1) if source else target
            hypothesis = [[source, target, template], result]
        else:
            hypothesis = goal = open_tree(goal[2], template, 2)
        floor -= 1
        hypothesis_image = floor if major or len(goal) % 2 == major else 0
        context += (open_tree(hypothesis, hypothesis_image),)
        goal = open_tree(goal, [floor])


try:
    read_instruction = load(open(0)).pop
    check(read_instruction(), ())
except Exception:
    print('REJECT')
    raise
print('ACCEPT')
