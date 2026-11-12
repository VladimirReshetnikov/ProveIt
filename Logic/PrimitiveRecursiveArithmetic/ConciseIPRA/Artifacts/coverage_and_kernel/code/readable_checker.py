"""Readable, self-contained expansion of the explicit-list complete checker.

Input is a JSON array, with the goal last and instruction packets before it.
Acceptance requires normal exit and the exact line ACCEPT.  The program
imports no theorem database, producer, or metatheoretic helper.
"""
import json


def check(goal, assumptions=[[]], floor=0):
    """Check a goal in an immutable-by-convention lexical proof context.

The initial empty-array assumption represents the derived theorem 0=0.
Neither the default list nor any caller's context is mutated.
"""
    def open_tree(tree, image=None, depth=0):
        if isinstance(tree, list):
            return [open_tree(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and open_tree(image, depth=3)

    if open_tree(goal) in assumptions:
        return

    major, source, initializer_or_mode, template_or_witness = instruction()
    check(major, assumptions, floor)

    equality = [source, initializer_or_mode]
    closure = not source and [template_or_witness] * 3
    replacement = (
        major in (equality, closure)
        and open_tree(template_or_witness, initializer_or_mode) == goal
        and open_tree(template_or_witness, source)
    )
    goal = replacement or goal

    if major:
        # A unary D major exports a Q resource.  Other arities export truth.
        hypothesis = major * 3
    elif initializer_or_mode:
        # Generated computation: a zero or successor instance of iteration.
        counter = source and [source]
        lhs = [counter, initializer_or_mode, template_or_witness]
        rhs = (open_tree(template_or_witness,
                         [source, initializer_or_mode, template_or_witness], 3)
               if source else initializer_or_mode)
        hypothesis = [lhs, rhs]
    else:
        # The witness must be opened at the old floor, before allocation.
        hypothesis = goal = open_tree(*goal, template_or_witness, 2)

    floor -= 1
    image = (major or len(goal) % 2 == initializer_or_mode) and floor
    check(open_tree(goal, [floor]),
          assumptions + [open_tree(hypothesis, image)], floor)


instruction = json.load(open(0)).pop
check(instruction())
print('ACCEPT')
