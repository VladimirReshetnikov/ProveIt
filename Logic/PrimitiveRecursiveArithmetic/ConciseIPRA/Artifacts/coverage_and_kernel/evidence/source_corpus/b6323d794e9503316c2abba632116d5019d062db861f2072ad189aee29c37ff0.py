"""Readable complete checker for the arity/predecessor certificate interface.
This explanatory program is not imported by the measured compact programs.
"""
import json

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    if isinstance(tree, list):
        return [open_tree(child, image, depth + 5 - len(tree))
                for child in tree]
    if fresh_floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=3)
    return 0


def check(goal, context):
    global fresh_floor
    if open_tree(goal) in context:
        return
    major, source, target, template = next_packet()
    if major:
        check(major, context)
        if major in ([source, target], not source and [template] * 3):
            if open_tree(template, target) == goal:
                goal = open_tree(template, source)
        local_assumption = major * 3
    elif major is None:
        # A predecessor is supplied; its successor is constructed internally.
        counter = source and [source]
        recursive_value = [source, target, template]
        result = (open_tree(template, recursive_value, 3)
                  if source else target)
        local_assumption = [[counter, target, template], result]
    else:
        # The splat admits unary paired introduction or the empty truth alias.
        local_assumption = goal = open_tree(*goal, template, 2)
    fresh_floor -= 1
    hypothesis_image = (fresh_floor
                        if major or len(goal) % 2 == major else 0)
    check(open_tree(goal, [fresh_floor]),
          context + [open_tree(local_assumption, hypothesis_image)])


next_packet = json.load(open(0)).pop
check(next_packet(), [])
print("ACCEPT")
