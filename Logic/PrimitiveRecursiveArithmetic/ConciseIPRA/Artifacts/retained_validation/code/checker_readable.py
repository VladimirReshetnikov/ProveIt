"""Explanatory expansion of checker.py; not the measured trusted module.

Preserves packet consumption, the three-argument opener interface, eager
missing-image validation, scope allocation and lazy source-instance choice.
"""


def check(context, goal):
    global floor
    packet = instruction()
    source, target, template, major = packet
    scanned = opening(goal)
    floor -= 1
    computation = [
        [[source] if source else 1, target, template],
        opening(template, packet[:3], 3) if source else target,
    ]
    if scanned in (floor, *context, computation):
        return

    # Prepare the introduction witness BEFORE checking the major proof.
    hypothesis = major * 3
    if not hypothesis:
        goal = opening(*goal, template, 2)
        hypothesis = goal
    major_result = check(context, major)
    mode = major_result or major or len(goal) == 2 == target
    image = mode and floor
    next_context = context + [opening(hypothesis, image)]

    # The target instance is still evaluated on every nonterminal call.
    expected = packet[:2] if source else [template] * 3
    target_instance = opening(template, target)
    matched = (major, goal) == (expected, target_instance)
    next_goal = opening(template, source) if matched else goal
    check(next_context, opening(next_goal, [floor]))


floor = 0


def opening(tree, image=check, depth=0):
    if tree * 0 == [] and (floor | (len(tree) in {1, 2 + depth % 2})):
        return [
            opening(child, image,
                    depth + (index & 2 if depth % 2 else 5 - len(tree)))
            for index, child in enumerate(tree)
        ]
    # The bitwise operation forces any RETAINED JSON scalar to int/bool.
    # Out-of-range floats can be holes, but cannot occur in a used image.
    if floor <= tree < depth and floor < (depth & (tree % 2)):
        return tree or 1
    # Keep multiplication eager: the missing-image sentinel must be tested
    # even at a formula hole, where depth % 2 is zero.
    return depth % 2 * opening(image, depth=3)


import json
instruction = json.load(open(0)).pop
check([[]], instruction())
print('ACCEPT')
