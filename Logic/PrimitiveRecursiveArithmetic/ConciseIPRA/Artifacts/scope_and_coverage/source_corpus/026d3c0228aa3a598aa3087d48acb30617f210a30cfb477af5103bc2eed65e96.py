"""Readable expansion of the strict triplicate checker.

This file is not imported by the measured kernel.  On JSON inputs it has
its successful behavior, with an explicit list test instead of a zero-product
list test.  Source and verdict handling are included in the compact kernel.
"""
from json import load

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    """Validate existing parameters and replace the exposed numerical slot.

    Formula roots have depth 0; numerical roots have depth 3.  Coordinates
    0, 1, 2 are numerical zero aliases.  Protected binder coordinates start
    at 3 and occur in pairs.  Negative labels identify allocated parameters.

    Array arities 1, 2, 3 add respectively 4, 3, 2 to the traversal depth.
    In the formula reading these are D, equality, and Q.  In the numerical
    reading they are successor, an inert zero annotation, and iteration.
    Larger arrays have constant readings: truth as formulas and zero as
    numerical terms.  Their children are traversed but ignored semantically.
    """
    if isinstance(tree, list):
        return [open_tree(child, image, depth + 5 - len(tree))
                for child in tree]
    if fresh_floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=3)
    return 0


def verify(goal, context):
    global fresh_floor
    if open_tree(goal) in context:
        return

    major, source, target_or_mode, template_or_witness = instruction()
    if major:
        verify(major, context)
        equality = [source, target_or_mode]
        closure = not source and [template_or_witness] * 3
        if major in (equality, closure):
            if open_tree(template_or_witness, target_or_mode) == goal:
                goal = open_tree(template_or_witness, source)
        # A unary D major exports its triplicated Q body.
        # Any other nonempty array exports arity >= 6, interpreted as truth.
        hypothesis = major * 3
    elif template_or_witness:
        # Exactly one positional element is present for a unary D goal.
        # A goal of arity >= 2 supplies too many arguments and rejects.
        # The empty-array case can only establish an already-true goal.
        hypothesis = goal = open_tree(*goal, template_or_witness, 2)
    else:
        predecessor, seed, update = source
        counter = [predecessor] if target_or_mode else target_or_mode
        lhs = [counter, seed, update]
        rhs = (open_tree(update, source, 3) if target_or_mode else seed)
        hypothesis = [lhs, rhs]

    fresh_floor -= 1
    image = (fresh_floor if major or len(goal) % 2 == major else 0)
    verify(open_tree(goal, [fresh_floor]),
           context + [open_tree(hypothesis, image)])


try:
    instruction = load(open(0)).pop
    verify(instruction(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
