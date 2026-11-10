"""Readable expansion of checker_predecessor_exit.py.

The whole compact checker is the measured trusted program. This separately
executable exposition adds no theorem library or arithmetic evaluator.
"""
from json import load

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    """Validate a tree and open its first exposed numerical coordinate.

    Even depths are formula positions; odd depths are numerical positions.
    Unary/binary/ternary nodes protect respectively one/zero/two slots.
    Negative coordinates name already allocated rigid numerical parameters.
    """
    if isinstance(tree, list):
        return [open_tree(child, image, depth + b' \x02\x01\x04'[len(tree)])
                for child in tree]
    if fresh_floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=1)
    return 0


def verify(goal, context):
    global fresh_floor
    if open_tree(goal) in context:
        return

    major, source, target, template = read_instruction()
    if major:
        verify(major, context)
        # Equality transport and conditional-closure specialization.
        if (major in ([source, target], not source and [template])
                and open_tree(template, target) == goal):
            goal = open_tree(template, source)
        # An equation/Q major adds truth; a D major opens a Q clause.
        local_assumption = major[2:]
    elif major is None:
        # A supplied predecessor determines a computation theorem.
        predecessor, seed, update = source, target, template
        if predecessor:
            counter = [predecessor]
            recursive_value = [predecessor, seed, update]
            result = open_tree(update, recursive_value, 1)
        else:
            counter = predecessor
            result = seed
        local_assumption = [[counter, seed, update], result]
    else:
        # [] selects case; numerical 0 permits progress on literal equations.
        # The witness template may itself be zero.
        local_assumption = goal = open_tree(goal[2], template, 2)

    fresh_floor -= 1
    next_goal = open_tree(goal, [fresh_floor])
    image = (fresh_floor if major or len(goal) % 2 == major else 0)
    next_assumption = open_tree(local_assumption, image)
    verify(next_goal, context + [next_assumption])


read_instruction = load(open(0)).pop
verify(read_instruction(), [])
print('ACCEPT')
