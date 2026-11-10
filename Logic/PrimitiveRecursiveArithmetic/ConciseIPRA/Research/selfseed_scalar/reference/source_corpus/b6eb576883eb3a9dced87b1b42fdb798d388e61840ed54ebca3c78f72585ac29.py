"""Complete readable affine-scope checker for the supplied iPRA calculus.

Only JSON and Python are used. Each list contributes its arity plus one to
scope depth. Equations therefore have one extra dummy numerical slot.
See the report for the mathematical decoder and canonical translation.
"""
from json import load

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    if isinstance(tree, list):
        return [open_tree(child, image, depth + len(tree) + 1)
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
    major, source, target, motive = instruction()
    if major:
        verify(major, context)
        if major in ([source, target], not source and [motive]):
            if open_tree(motive, target) == goal:
                goal = open_tree(motive, source)
        hypothesis = major[2:]
    elif motive:
        # Exact arity is essential: larger formula arities denote absurdity.
        annotation0, annotation1, matrix = goal
        hypothesis = goal = open_tree(matrix, motive, 2)
    else:
        predecessor, seed, update = source
        counter = target and [predecessor]
        result = open_tree(update, source, 1) if target else seed
        hypothesis = [[counter, seed, update], result]
    fresh_floor -= 1
    if major or len(goal) % 2 == major:
        hypothesis_image = fresh_floor
    else:
        hypothesis_image = 0
    verify(open_tree(goal, [fresh_floor]),
           context + [open_tree(hypothesis, hypothesis_image)])


try:
    instruction = load(open(0)).pop
    verify(instruction(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
