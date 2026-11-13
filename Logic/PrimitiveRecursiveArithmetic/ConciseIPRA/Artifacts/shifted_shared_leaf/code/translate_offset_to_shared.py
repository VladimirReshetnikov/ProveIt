"""Untrusted successful-trace converter: offset472 -> shifted shared468.

Usage: python3 code/translate_offset_to_shared.py < old.json > new.json

The source is the inherited offset472 integer/list certificate protocol:
four-field instructions followed by [closed guarded goal, 0], consumed
right to left. The converter simulates a successful source execution,
inserts [0,0,0,0] at each hypothesis leaf, and retains the existing
instruction at every other call. It leaves the public goal and initial
scope unchanged. Unused source prefixes are omitted.

This file is not part of the measured checker or its trusted base. It
does not validate the public guarded grammar or prove the source sound.
Check its result with the standalone checker.py. Nonacceptance and
resource exhaustion in the source simulation cause conversion to fail.
"""
import copy
import json
import sys

MISSING = object()


def convert(certificate):
    if type(certificate) is not list or not certificate:
        raise ValueError('Expected a nonempty packet stack')
    root = copy.deepcopy(certificate[-1])
    if (type(root) is not list or len(root) != 2
            or type(root[1]) is not int or root[1] != 0):
        raise ValueError('The terminal item must be [goal, 0]')
    pending = copy.deepcopy(certificate[:-1])
    emitted = []
    stats = {'source_packets': 0, 'hypothesis_packets': 0, 'calls': 0}

    def check(context, goal, floor):
        def opening(tree, image=MISSING, depth=2):
            if type(tree) is list:
                return [opening(child, image, depth + 5 - len(tree))
                        for child in tree]
            if type(tree) is not int:
                raise ValueError('Expected an exact integer/list tree or a supplied image')
            if floor <= tree < depth:
                return tree
            # Multiplication is deliberately eager, including at even depth.
            return depth % 2 * opening(image, depth=5)

        stats['calls'] += 1
        if opening(goal) in context:
            emitted.append([0, 0, 0, 0])
            stats['hypothesis_packets'] += 1
            return True

        packet = pending.pop()
        major, source, seed, template = packet
        emitted.append(copy.deepcopy(packet))
        stats['source_packets'] += 1
        recursive_term = [source, seed, template]
        computation = [
            [source and [source], seed, template],
            opening(template, recursive_term, 5) if source else seed,
        ]
        if goal == computation:
            return True

        check(context, major, floor)
        hypothesis = major * 3
        if not hypothesis:
            goal = opening(*goal, template, 4)
            hypothesis = goal
        progressive = any((major, 3 % len(goal)))
        floor -= 1
        hypothesis = opening(hypothesis, progressive * floor)
        minor = opening(template, source)
        required_major = [source, seed] if source else [template] * 3
        target = opening(template, seed)
        if (major, goal) == (required_major, target):
            goal = minor
        goal = opening(goal, [floor])
        return check(context + [hypothesis], goal, floor)

    check([0], *root)
    stats['new_packets'] = len(emitted)
    stats['unused_source_prefix_items'] = len(pending)
    if stats['new_packets'] != stats['source_packets'] + stats['hypothesis_packets']:
        raise AssertionError('Internal trace accounting error')
    return list(reversed(emitted)) + [root], stats


if __name__ == '__main__':
    translated, statistics = convert(json.load(sys.stdin))
    json.dump(translated, sys.stdout, separators=(',', ':'))
    sys.stdout.write('\n')
    print(json.dumps(statistics, sort_keys=True), file=sys.stderr)
