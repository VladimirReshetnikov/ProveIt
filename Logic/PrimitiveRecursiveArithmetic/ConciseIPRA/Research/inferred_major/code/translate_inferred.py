"""Translate a successful inferred-major certificate to its frozen control.

This is an untrusted certificate producer, not acceptance code.  Both source
and target standalone modules must be run separately to check the result.
It operates on the canonical finite integer/list proof interface.  An unused
prefix is copied verbatim.  The local/global protocols differ only in their
fresh-parameter state and neutral-major handling, matching the frozen sources.
"""
import argparse
import copy
import json
from pathlib import Path


def translate(data, protocol="local"):
    if protocol not in ("local", "global"):
        raise ValueError("protocol must be local or global")
    result = copy.deepcopy(data)
    pending = list(enumerate(copy.deepcopy(data)))
    clock = 0
    changes = []
    steps = []

    def consume():
        return pending.pop()

    def check(goal, context, floor=0):
        nonlocal clock

        def opening(tree, image=None, depth=0):
            try:
                return [opening(child, image, depth + 5 - len(tree))
                        for child in tree]
            except Exception:
                lower = clock if protocol == "global" else floor
                return tree if lower <= tree < depth else depth % 2 and opening(image, depth=3)

        while opening(goal) not in context:
            index, packet = consume()
            major, source, initializer, template = packet
            old_major = copy.deepcopy(major)
            matched = opening(template, initializer) == goal
            if matched:
                major = [source, initializer] if source else [template] * 3
                goal = opening(template, source)
            result[index] = [major, source, initializer, template]
            if major != old_major:
                changes.append(index)
            steps.append({"index": index, "target_matched": matched,
                          "major_changed": major != old_major})
            if protocol == "global":
                if major:
                    check(major, context)
                    hypothesis = major * 3
                elif initializer:
                    hypothesis = [[source and [source], initializer, template],
                                  opening(template, [source, initializer, template], 3)
                                  if source else initializer]
                else:
                    goal = opening(*goal, template, 2)
                    hypothesis = goal
                clock -= 1
                fresh = clock
            else:
                check(major, context, floor)
                if major:
                    hypothesis = major * 3
                elif initializer:
                    hypothesis = [[source and [source], initializer, template],
                                  opening(template, [source, initializer, template], 3)
                                  if source else initializer]
                else:
                    goal = opening(*goal, template, 2)
                    hypothesis = goal
                floor -= 1
                fresh = floor
            context += (opening(hypothesis, (major or len(goal) == 2) and fresh),)
            goal = opening(goal, [fresh])

    _, goal = consume()
    check(goal, () if protocol == "global" else (0,))
    return result, {"protocol": protocol, "steps": len(steps),
                    "changed_indices": changes, "trace": steps,
                    "unused_prefix_length": len(pending)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--protocol", choices=("local", "global"), default="local")
    arguments = parser.parse_args()
    certificate, trace = translate(json.loads(arguments.source.read_text()), arguments.protocol)
    arguments.destination.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    print(json.dumps(trace, indent=2))
