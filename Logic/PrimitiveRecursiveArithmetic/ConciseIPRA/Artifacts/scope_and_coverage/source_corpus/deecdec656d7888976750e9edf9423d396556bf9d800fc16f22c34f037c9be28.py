"""Complete readable checker for predecessor-specified computations.

Equivalent successful behavior to checker_joint.py. The
opener accepts empty strings/dictionaries as zero aliases, and an object
with only the empty-string key as a unary zero alias; its value is ignored.
Nonempty string keys reject when traversed. JSON is data, never code.
"""
import json

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    try:
        # The zero-arity increment is never used: there are no children.
        increment = (0, 2, 1, 4)
        return [open_tree(child, image, depth + increment[len(tree)])
                for child in tree]
    except:
        if fresh_floor <= tree < depth:
            return tree
        if depth % 2:
            return open_tree(image, depth=1)
        return 0


def verify(goal, context):
    global fresh_floor
    if open_tree(goal) in context:
        return
    major, source, target, template = instruction()
    if major:
        verify(major, context)
        recognized = major in ([source, target], not source and [template])
        if recognized and open_tree(template, target) == goal:
            goal = open_tree(template, source)
        hypothesis = major[2:]
    elif template:
        hypothesis = goal = open_tree(goal[2], template, 2)
    else:
        predecessor, initial, update = source
        counter = [predecessor] if predecessor else predecessor
        result = open_tree(update, source, 1) if predecessor else initial
        hypothesis = [[counter, initial, update], result]
    fresh_floor -= 1
    progress = major or len(goal) % 2 == major
    image = fresh_floor if progress else 0
    verify(open_tree(goal, [fresh_floor]),
           context + [open_tree(hypothesis, image)])


try:
    instruction = json.load(open(0)).pop
    verify(instruction(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
