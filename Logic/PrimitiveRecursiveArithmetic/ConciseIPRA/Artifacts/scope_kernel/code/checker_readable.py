"""Full native Eq/Q/D checker, with whole-certificate integer/list validation.

Read a JSON array containing proof packets followed by the closed conclusion.
Packets are consumed from right to left. Success is normal exit and ACCEPT.
An exception rejects. No axiom database or external producer is imported.
"""
import json


def valid(value, depth=0):
    # Mode 0 checks exact integer/list syntax. Mode starting at 2 checks
    # public formula shape and numerical slot parity. The first opening
    # in check() supplies the slot upper bounds, before reading a packet.
    if type(value) is int:
        return (depth == 0 or
                depth % 2 and (value == 0 or
                               value > 2 and value % 2))
    if type(value) is not list:
        return False
    if depth:
        # At even formula depth: D, equality, or a diagonal Q triple.
        # At odd numerical depth: successor or iterator. A diagonal
        # triple is already a permitted iterator in that case.
        if not (len(value) in (1, 2 + depth % 2) or
                value == [value[0]] * 3):
            return False
    child_depth = depth + 5 - len(value) if depth else 0
    return all(valid(child, child_depth) for child in value)


def check(goal, context=(0,), floor=0):
    def opening(value, image=None, depth=0):
        if isinstance(value, list):
            return [opening(child, image, depth + 5 - len(value))
                    for child in value]
        if floor <= value < depth:
            return value
        # Formula padding is truth. A used numerical image is checked
        # at numerical root depth 3 before being substituted.
        return depth % 2 and opening(image, depth=3)

    if opening(goal) in context:
        return
    major, source, seed_or_mode, template_or_witness = instruction()
    expected_major = ([source, seed_or_mode] if source else
                      [template_or_witness] * 3)
    if major == expected_major:
        if opening(template_or_witness, seed_or_mode) == goal:
            replacement = opening(template_or_witness, source)
            if replacement:
                goal = replacement

    check(major, context, floor)
    if major:
        local = major * 3
    elif seed_or_mode:
        lhs = [source and [source], seed_or_mode, template_or_witness]
        rhs = (opening(template_or_witness,
                       [source, seed_or_mode, template_or_witness], 3)
               if source else seed_or_mode)
        local = [lhs, rhs]
    else:
        goal = opening(*goal, template_or_witness, 2)
        local = goal

    floor -= 1
    image = (major or len(goal) % 2 == seed_or_mode) and floor
    check(opening(goal, [floor]), context + (opening(local, image),), floor)


*certificate, conclusion = json.load(open(0))
if not (valid(certificate) and valid(conclusion, 2)):
    raise ValueError('The certificate must use integer/list syntax and have a canonical closed goal')
instruction = certificate.pop
check(conclusion)
print('ACCEPT')
