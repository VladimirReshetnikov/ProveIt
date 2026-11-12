"""Standalone typed checker for the root-reversal presentation of iPRA.

Input is a JSON list of instruction packets followed by a canonical closed
Eq/Q/D goal. Packets are consumed from right to left. Each packet contains
[major, source, initializer_or_mode, template_or_witness]. Every JSON node
must have exact type int or list; booleans are not numerical syntax.

The initial scalar formula 0 is administrative truth. A formula triple is
read symmetrically as the conjunction of its three conditional closures;
canonical Q formulas have three identical entries. Root reversal therefore
reverses an equation, preserves D, and reorders Q conjuncts. It is sound on
noncanonical internal triples as well as canonical public formulas.

The compact selected program has the same algorithm. This expansion is
separately standalone: it imports no producer, proof database or helper.
"""
import json


def integer_list_tree(value):
    return type(value) is int or (
        type(value) is list and all(integer_list_tree(child) for child in value)
    )


def canonical(value, depth=0):
    """Even depths check formulas; odd depths check numerical terms."""
    if type(value) is int:
        return depth % 2 and (
            value == 0 or 3 <= value < depth and value % 2
        )
    if type(value) is not list:
        return False
    arity = len(value)
    if arity not in ([1, 3] if depth % 2 else [1, 2, 3]):
        return False
    if not depth % 2 and arity == 3 and value != [value[0]] * 3:
        return False
    return all(canonical(child, depth + 5 - arity) for child in value)


def check(goal, assumptions=(0,), floor=0):
    def open_tree(tree, image=check, depth=0):
        if type(tree) is list:
            return [open_tree(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and open_tree(image, depth=3)

    if open_tree(goal) in assumptions:
        return
    major, source, initializer_or_mode, template_or_witness = instruction()

    expected_major = ([source, initializer_or_mode] if source
                      else [template_or_witness] * 3)
    if major == expected_major:
        target = open_tree(template_or_witness, initializer_or_mode)
        if target == goal[::-1]:
            goal = open_tree(template_or_witness, source)

    check(major, assumptions, floor)
    if major:
        supplied = major * 3
    elif initializer_or_mode:
        counter = source and [source]
        lhs = [counter, initializer_or_mode, template_or_witness]
        rhs = (open_tree(template_or_witness,
                         [source, initializer_or_mode, template_or_witness], 3)
               if source else initializer_or_mode)
        supplied = [lhs, rhs]
    else:
        goal = open_tree(*goal, template_or_witness, 2)
        supplied = goal

    floor -= 1
    image = (major or len(goal) % 2 == initializer_or_mode) and floor
    conclusion = open_tree(goal, [floor])
    extended = assumptions + (open_tree(supplied, image),)
    check(conclusion, extended, floor)


certificate = json.load(open(0))
if not integer_list_tree(certificate):
    raise ValueError('Only integer/list certificate syntax is allowed')
instruction = certificate.pop
goal = instruction()
if not canonical(goal):
    raise ValueError('The goal is not a canonical closed formula')
check(goal)
print('ACCEPT')
