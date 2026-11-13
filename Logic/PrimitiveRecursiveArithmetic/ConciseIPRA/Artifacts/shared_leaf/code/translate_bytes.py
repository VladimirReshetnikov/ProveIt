"""Untrusted successful-trace compiler for membership470 from direct-leaf474.

It preserves the public goal and initial scope floor literally.  Inserted
hypothesis packets have no new assumptions and allocate no fresh names.
No function here is imported by a measured checker.
"""
import ast
import copy
import json
from pathlib import Path
import sys

CONTROL = Path(__file__).resolve().parents[1] / 'controls/checker_bytes.py'
DUMMY = [[], 0, 0, 0]


def opened(a, k, image=None, depth=0):
    """Exact integer/list, eager, missing-image version of the byte opener."""
    if type(a) is list:
        return [opened(b, k, image, depth + 5 - len(a)) for b in a]
    if type(a) is not int:
        raise ValueError('not an integer/list tree or absent image')
    if k <= a < depth:
        return a
    return (depth % 2) * opened(image, k, depth=3)


def convert(data):
    pending = copy.deepcopy(data[:-1])
    root = copy.deepcopy(data[-1])
    emitted = []
    stats = {'source_packets': 0, 'hypothesis_packets': 0, 'calls': 0}

    def pop():
        packet = pending.pop()
        emitted.append(copy.deepcopy(packet))
        stats['source_packets'] += 1
        return packet

    env = {'q': pop}
    tree = ast.parse(CONTROL.read_text())
    exec(compile(ast.Module(body=tree.body[:2], type_ignores=[]), str(CONTROL), 'exec'), env)
    original = env['c']

    def wrapped(g, a, k):
        stats['calls'] += 1
        if opened(a, k) in g:
            emitted.append(copy.deepcopy(DUMMY))
            stats['hypothesis_packets'] += 1
        return original(g, a, k)

    env['c'] = wrapped
    wrapped([[]], *root)
    stats['new_packets'] = len(emitted)
    stats['unused_source_prefix_items'] = len(pending)
    return list(reversed(emitted)) + [root], stats


if __name__ == '__main__':
    source, target = map(Path, sys.argv[1:])
    compiled, stats = convert(json.loads(source.read_text()))
    target.write_text(json.dumps(compiled, separators=(',', ':')) + '\n')
    print(json.dumps(stats, sort_keys=True))
