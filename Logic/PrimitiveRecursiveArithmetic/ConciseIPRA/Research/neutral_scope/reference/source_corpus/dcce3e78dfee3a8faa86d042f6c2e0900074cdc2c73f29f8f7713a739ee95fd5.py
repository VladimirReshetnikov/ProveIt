"""Standalone readable checker for the regular four-field proof protocol.

All input is JSON data. No proof producer, compiler, symbolic arithmetic
package, or test module is imported. The compact regular profile uses
the same rules; kernel_bytes.py additionally uses elimination-only
assumptions and therefore has a different canonical certificate compiler.
"""
import json

fresh_floor = 0


def open_tree(tree, image=None, depth=0):
    """Validate/open the inherited sorted, protected-slot numerical syntax."""
    if isinstance(tree, list):
        increment = b" \2\1\4"[len(tree)]
        return [open_tree(child, image, depth + increment) for child in tree]
    if fresh_floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=1)
    return 0


def verify(goal, context):
    """Normal return is success; any exception is rejection."""
    global fresh_floor
    if open_tree(goal) in context:
        return
    major, source, target, template = instruction()
    if major:
        verify(major, context)
        local_hypothesis = major[2:]
        recognized_equation = major == [source, target]
        recognized_closure = not source and major == [template]
        if (recognized_equation or recognized_closure) and open_tree(template, target) == goal:
            goal = open_tree(template, source)
        # For a proved equation or unary closure, a failed match keeps
        # the requested goal unchanged and the hypothesis is [] (truth).
        # For a paired formula, the hypothesis is its unary closure and
        # the goal is unchanged: this is ordinary paired elimination.
    elif template:
        local_hypothesis = goal = open_tree(goal[2], template, 2)
    else:
        (counter, initializer, update), result = goal
        if counter:
            predecessor, = counter
            counter_opened = open_tree(update, predecessor, 3)
            initializer = open_tree(counter_opened, [predecessor, initializer, update], 1)
        else:
            initializer = [initializer]
        if result != initializer:
            raise ValueError('Incorrect computation equation')
        return

    fresh_floor -= 1
    hypothesis_image = fresh_floor if major or len(goal) % 2 == major else 0
    verify(open_tree(goal, [fresh_floor]),
           context + [open_tree(local_hypothesis, hypothesis_image)])


try:
    instruction = json.load(open(0)).pop
    verify(instruction(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
