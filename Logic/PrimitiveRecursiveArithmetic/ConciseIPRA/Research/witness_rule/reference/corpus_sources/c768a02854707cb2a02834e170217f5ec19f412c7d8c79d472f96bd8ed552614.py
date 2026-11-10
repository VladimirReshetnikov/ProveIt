"""Readable equivalent of checker.py, including its complete verdict driver.

Only JSON parsing is imported.  Every proof instruction is data.  The local
scope floor is passed to major premises by value and restored automatically
when they return.  There is no mutable global eigenparameter allocator.
"""
import json


def check(goal, context, floor=0):
    def open_tree(tree, image=None, depth=0):
        # On JSON values this test selects exactly lists.  Other unsupported
        # used values raise below.  Retaining it preserves the compact
        # program's precise boundary, including its harmless numeric aliases.
        if tree * 0 == []:
            increment = (32, 2, 1, 4)[len(tree)]
            return [open_tree(child, image, depth + increment)
                    for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and open_tree(image, depth=1)

    if open_tree(goal) in context:
        return
    major, source, target, template = pop()
    if major:
        # check has its own floor binding: its local allocations cannot
        # change the caller's floor after this premise has completed.
        check(major, context, floor)
        if major in ([source, target], not source and [template]):
            if open_tree(template, target) == goal:
                goal = open_tree(template, source)
        hypothesis = major[2:]
    elif template:
        # The numerical witness is checked before allocating the step name.
        goal = open_tree(goal[2], template, 2)
        hypothesis = goal
    else:
        counter, seed, update = source
        if counter:
            # The eager inner opening checks the predecessor shape and seed,
            # even when the update does not use its recursive-state argument.
            recursive_state = open_tree([*counter, seed, update], depth=1)
            result = open_tree(update, recursive_state, 1)
        else:
            result = seed
        hypothesis = [source, result]
    floor -= 1
    step_goal = open_tree(goal, [floor])
    image = floor if major or len(goal) % 2 == major else 0
    opened_hypothesis = open_tree(hypothesis, image)
    check(step_goal, context + [opened_hypothesis], floor)


try:
    pop = json.load(open(0)).pop
    check(pop(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
