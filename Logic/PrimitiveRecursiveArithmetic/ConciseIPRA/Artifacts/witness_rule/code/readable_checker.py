"""Readable expansion of the deterministic-witness checker.

The compact comparison profile is checker.py. Neither program imports the
other, the named producer, the normalizer, or a table of arithmetic axioms.
Success requires both exit status zero and exactly ACCEPT on standard output.
"""
import json

floor = 0


def opening(tree, image=0j, depth=0):
    """Validate and open the inherited sorted arity representation.

    Formula roots have depth zero; numerical roots have depth three.
    At meaningful nodes, 5 - arity accounts for binder and dummy slots.
    The complex default is an invalid numerical image: attempting to use
    it at a numerical hole fails the ordered comparison below.
    """
    if isinstance(tree, list):
        return [opening(child, image, depth + 5 - len(tree))
                for child in tree]
    if floor <= tree < depth:
        return tree
    return depth % 2 and opening(image, depth=3)


def check(goal, context):
    global floor
    if opening(goal) in context:
        return

    major, source, target, template = instruction()
    if major:
        check(major, context)
        matches = major in ([source, target], not source and [template] * 3)
        if matches and opening(template, target) == goal:
            # The compact program retains the unchanged obligation if a
            # noncanonical source opening is falsy. Canonical matrices
            # are nonempty, so this fallback does not affect completeness.
            goal = opening(template, source) or goal

    exported = major * 3
    if exported:
        local = exported
    elif target:
        predecessor, seed, update = source, target, template
        counter = predecessor and [predecessor]
        endpoint = (opening(update, [predecessor, seed, update], 3)
                    if predecessor else seed)
        local = [[counter, seed, update], endpoint]
    else:
        goal = opening(*goal, template, 2)
        local = goal

    floor -= 1
    # Progress is selected only at a literal equation with literal-zero
    # witness. All other canonical introductions select the base case.
    # For computation, this is the inherited known-zero-instance supply.
    local_image = (major or template == len(goal) % 2 == 0) and floor
    check(opening(goal, [floor]), context + [opening(local, local_image)])


instruction = json.load(open(0)).pop
check(instruction(), [])
print('ACCEPT')
