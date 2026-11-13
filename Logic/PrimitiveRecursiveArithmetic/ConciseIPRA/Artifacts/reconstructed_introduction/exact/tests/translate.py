"""Untrusted canonical-certificate compiler from the actual-binding entry core to the intrinsic phase core.

The caller supplies a successful canonical three-field entry-reservation
certificate. Only source-zero INTRODUCTION records are changed to an empty
list source. Zero-computation and closure-specialization sources stay zero.
The proof language's arbitrary aliases are outside this compiler's contract.
"""

import copy

MISSING = object()


def translate(document):
    stack = copy.deepcopy(document)
    result = copy.deepcopy(document)
    floor = 0
    stats = {"nodes": 0, "leaves": 0, "introductions": 0,
             "matched_eliminations": 0, "unmatched_eliminations": 0}

    def opening(tree, image=MISSING, depth=0):
        if type(tree) is list and (floor or len(tree) in (1, 2 + depth % 2)):
            return [opening(child, image, depth + (2 * (j == 2) if depth % 2 else 5 - len(tree)))
                    for j, child in enumerate(tree)]
        if floor <= tree < depth and (floor or depth & (tree % 2)):
            return tree or 1
        return (depth % 2 or not floor) and opening(image, depth=3)

    def check(context, goal):
        nonlocal floor
        index = len(stack) - 1
        source, mode, template = record = stack.pop()
        stats["nodes"] += 1
        checked = opening(goal)
        floor -= 1
        computation = [[source and [source] or 1, mode, template],
                       opening(template, record, 3) if source else mode]
        if checked in (floor, *context, computation):
            stats["leaves"] += 1
            return
        if opening(template, mode) == goal:
            goal = opening(template, source)
            source = record[:2] if source else [template] * 3
            stats["matched_eliminations"] += 1
        elif source:
            stats["unmatched_eliminations"] += 1
        else:
            if record[0] != 0:
                raise ValueError("Expected the canonical scalar-neutral source")
            result[index][0] = []
            stats["introductions"] += 1

        hypothesis = source * 3
        if not hypothesis:
            goal = opening(*goal, template, 2)
            hypothesis = goal
        check(context, source)
        image = floor if source or len(goal) == 2 == mode else 0
        hypothesis = opening(hypothesis, image)
        goal = opening(goal, [floor])
        check([*context, hypothesis], goal)

    check([0], stack.pop())
    stats["unused_prefix"] = len(stack)
    return result, stats


if __name__ == "__main__":
    import json
    import sys
    from pathlib import Path

    compiled, receipt = translate(json.loads(Path(sys.argv[1]).read_text()))
    Path(sys.argv[2]).write_text(json.dumps(compiled, separators=(",", ":")) + "\n")
    print(json.dumps(receipt))
