"""Standalone readable expansion of the explicit array-truth checker.

The initial [] formula denotes the inherited theorem 0=0. Every absent
major is encoded by []; the verifier checks it by the ordinary hypothesis
rule. A certificate is a JSON stack: its last element is the goal; earlier
four-field packets are consumed backwards. Unused prefix packets are inert.
Success means exit zero and exactly ACCEPT. An exception rejects.
"""
import json

fresh_floor = 0


def opening(tree, image=None, depth=0):
    if isinstance(tree, list):
        return [opening(child, image, depth + 5 - len(tree))
                for child in tree]
    if fresh_floor <= tree < depth:
        return tree
    return depth % 2 and opening(image, depth=3)


def verify(goal, context):
    global fresh_floor
    if opening(goal) in context:
        return
    major, source, target_or_mode, template = instruction()
    verify(major, context)
    if (major in ([source, target_or_mode], not source and [template] * 3)
            and opening(template, target_or_mode) == goal):
        replacement = opening(template, source)
        if replacement:
            goal = replacement
    if major:
        hypothesis = major * 3
    elif target_or_mode:
        predecessor, seed, update = source, target_or_mode, template
        counter = predecessor and [predecessor]
        result = (opening(update, [predecessor, seed, update], 3)
                  if predecessor else seed)
        hypothesis = [[counter, seed, update], result]
    else:
        # Here target_or_mode must be false-valued. Mode 0 selects
        # progress only for a literal equation; [] selects numerical cases.
        # A truthy mode instead selects computation above, never progress.
        hypothesis = goal = opening(*goal, template, 2)
    fresh_floor -= 1
    continuation_goal = opening(goal, [fresh_floor])
    image = (major or len(goal) % 2 == target_or_mode) and fresh_floor
    verify(continuation_goal, context + [opening(hypothesis, image)])


instruction = json.load(open(0)).pop
verify(instruction(), [[]])
print('ACCEPT')
