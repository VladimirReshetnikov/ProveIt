"""Readable expansion of arity_explicit_p.py.

This is a composition of the inherited arity decoder, uniform-predecessor
packets, and exit-status driver. No arithmetic evaluator is imported.
Canonical formulas: Eq=[s,t], D=[body], Q=[body,body,body].
Canonical numerical terms: zero, successor [n], scalar iteration [n,a,h].
"""
import json

floor = 0


def opening(tree, image=None, depth=0):
    """Validate and open a sorted arity tree at its meaningful positions.

    The inherited arity decoder uses numerical base depth three. Larger
    arrays have constant interpretations (truth at formula roots, zero at
    numerical roots); the soundness invariant is conditional on successful
    opening at a meaningful root, not on raw-tree idempotence.
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
        if (major in ([source, target], not source and [template] * 3)
                and opening(template, target) == goal):
            goal = opening(template, source)
        # A unary D major exports its Q body. Other nonempty arrays export
        # a larger-arity formula with the inherited constant-truth meaning.
        local = major * 3
    elif major is None:
        predecessor, seed, update = source, target, template
        counter = predecessor and [predecessor]
        result = (opening(update, [predecessor, seed, update], 3)
                  if predecessor else seed)
        local = [[counter, seed, update], result]
    else:
        # Nonempty goals must be unary paired formulas. An empty goal means
        # truth and is harmless. Case covers all canonical matrices; the
        # continuation selects progress only for literal equations.
        local = goal = opening(*goal, template, 2)
    floor -= 1
    successor_goal = opening(goal, [floor])
    local_image = floor if major or len(goal) % 2 == major else 0
    check(successor_goal, context + [opening(local, local_image)])


instruction = json.load(open(0)).pop
check(instruction(), [])
print('ACCEPT')
