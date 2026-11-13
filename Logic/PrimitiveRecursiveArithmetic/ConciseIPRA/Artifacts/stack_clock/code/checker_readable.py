"""Complete exact-public checker with scope derived from packet consumption.

Only packets mutate. initial_count is fixed after the public goal is removed.
The arithmetic and logical rules are those of the pinned retained-value control.
"""
import json

MISSING = object()


def opening(tree, image=MISSING, depth=0):
    floor = len(packets) - initial_count
    if tree * 0 == [] and (floor or len(tree) in (1, 2 + depth % 2)):
        return [opening(child, image,
                        depth + (index & 2 if depth % 2 else 5 - len(tree)))
                for index, child in enumerate(tree)]
    if floor <= tree < depth and floor < (depth & (tree % 2)):
        return tree or 1
    # This validates the image even when an even slot erases it.
    return (depth % 2) * opening(image, depth=3)


def check(context, goal):
    # The original counter advanced after this scan. Consuming the packet now
    # advances the derived floor by precisely one.
    scanned = opening(goal)
    source, target, template, major = record = packets.pop()
    computation = [
        [[source] if source else 1, target, template],
        opening(template, record[:3], 3) if source else target,
    ]
    if scanned in [*context, computation]:
        return

    # A witness must be instantiated before the compulsory major proof.
    hypothesis = major * 3
    if not hypothesis:
        goal = opening(*goal, template, 2)
        hypothesis = goal

    check(context, major)
    fresh = len(packets) - initial_count
    image = fresh if major or len(goal) == 2 == target else 0
    next_context = context + [opening(hypothesis, image)]

    # Preserve the control's delayed endpoint and lazy selected-source checks.
    expected_major = record[:2] if source else [template] * 3
    target_instance = opening(template, target)
    selected = opening(template, source) if (major, goal) == (expected_major, target_instance) else goal
    next_goal = opening(selected, [fresh])
    check(next_context, next_goal)


packets = json.load(open(0))
conclusion = packets.pop()
initial_count = len(packets)
check([[]], conclusion)
print('ACCEPT')
