"""Readable local checker for the inferred-major certificate protocol.

Public contract: a closed canonical guarded Eq/D formula, encoded by the
protected-slot arity representation described in the accompanying paper.
Consumed syntax is finite integer/list data.  This explanatory module is
standalone but is not one of the size records.  checker_native.py separately
retains and measures the incumbent native public-goal validation contract.
"""
import json


def check(goal, context=(0,), floor=0):
    def opening(tree, image=None, depth=0):
        if isinstance(tree, list):
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if type(tree) is not int:
            raise ValueError("expected a numerical coordinate or an array")
        if floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)

    while opening(goal) not in context:
        major, source, initializer, template = instruction()

        # This is the new protocol: the conclusion determines the major.
        # The packet's first field is ignored for this elimination step.
        if opening(template, initializer) == goal:
            major = [source, initializer] if source else [template] * 3
            goal = opening(template, source)

        # Reconstruction never grants the major as an assumption.
        # Its proof is checked in the original, unchanged context.
        check(major, context, floor)
        if major:
            hypothesis = major * 3
        elif initializer:
            predecessor = source
            counter = [predecessor] if predecessor else predecessor
            recursive_term = [predecessor, initializer, template]
            endpoint = (opening(template, recursive_term, 3)
                        if predecessor else initializer)
            hypothesis = [[counter, initializer, template], endpoint]
        else:
            goal = opening(*goal, template, 2)
            hypothesis = goal

        # Freshness has two phases: the old floor above, the new floor below.
        floor -= 1
        hypothesis_image = floor if major or len(goal) == 2 else 0
        context += (opening(hypothesis, hypothesis_image),)
        goal = opening(goal, [floor])


instruction = json.load(open(0)).pop
check(instruction())
print("ACCEPT")
