"""Standalone explanatory version of the generated-source checker.

Canonical arithmetic packets supply [counter, seed, update] and a step flag.
The source counter is generated as zero or successor(counter). The update
has one previous-state variable, with two raw aliases; there is no old-counter
argument. A generated equation needs a true zero instance, not universal truth
in the freshly allocated name. This program preserves the compact checker's
opening guards, annotation policy, hypothesis tests, and shared continuation.
"""
from json import load

floor = 0


def open_tree(tree, image=None, depth=0):
    """Validate finite sorted syntax and open its exposed numerical slots."""
    if isinstance(tree, list):
        increment = (32, 2, 1, 4)[len(tree)]
        return [open_tree(child, image, depth + increment) for child in tree]
    if floor <= tree < depth:
        return tree
    if depth % 2:
        return open_tree(image, depth=1)
    return 0


def check(goal, context):
    global floor
    if open_tree(goal) in context:
        return
    major, source, target, template = pop()
    if major:
        check(major, context)
        equality_or_closure = major in (
            [source, target], not source and [template]
        )
        if equality_or_closure and open_tree(template, target) == goal:
            goal = open_tree(template, source)
        hypothesis = major[2:]
    elif template:
        hypothesis = goal = open_tree(goal[2], template, 2)
    else:
        counter, seed, update = source
        step_flag = target
        # A canonical flag is 0 or 1. Keeping the exact false flag here
        # also preserves the compact program's treatment of raw aliases.
        generated_counter = step_flag and [counter]
        generated_source = [generated_counter, seed, update]
        if step_flag:
            # If an exposed state slot is used, open_tree validates the
            # entire supplied recursive value at numerical root. If no
            # such slot is used, the update is independent of that value.
            computed_target = open_tree(update, source, 1)
        else:
            computed_target = [seed]
        hypothesis = [generated_source, computed_target]
    floor -= 1
    step_goal = open_tree(goal, [floor])
    hypothesis_image = floor if major or len(goal) % 2 == major else 0
    local_hypothesis = open_tree(hypothesis, hypothesis_image)
    check(step_goal, context + [local_hypothesis])


try:
    pop = load(open(0)).pop
    check(pop(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
