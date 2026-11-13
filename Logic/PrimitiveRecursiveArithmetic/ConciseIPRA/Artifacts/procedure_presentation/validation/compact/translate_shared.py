"""Add the shared-leaf dummy packets to an accepted offset472 proof.

This is an untrusted convenience compiler, not part of any checker.
It preserves the offset codec and the public header. The new checker
validates the produced proof independently.
"""
import ast
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent


def load_kernel(path):
    tree = ast.parse(path.read_text())
    tree.body = [node for node in tree.body
                 if isinstance(node, ast.FunctionDef)
                 or isinstance(node, ast.Assign)
                 and any(isinstance(t, ast.Name) and t.id == 'c'
                         for t in node.targets)]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


def translate(certificate):
    stack = copy.deepcopy(certificate)
    header = stack.pop()
    if not isinstance(header, list) or len(header) != 2 or header[1] != 0:
        raise ValueError('Expected the canonical [closed_goal, 0] header')
    namespace = load_kernel(ROOT / 'controls/offset472.py')
    function = namespace['c']
    events = []
    dummy = [0, 0, 0, 0]

    def packet():
        value = stack.pop()
        events.append(copy.deepcopy(value))
        return value

    def profile(frame, event, _):
        if event != 'call' or frame.f_code is not function.__code__:
            return
        context, goal, floor = (frame.f_locals[name] for name in ('g', 'a', 'k'))

        def opening(tree, image=function, depth=2):
            if tree * 0 != 0:
                return [opening(child, image, depth + 5 - len(tree)) for child in tree]
            return tree if floor <= tree < depth else depth % 2 * opening(image, depth=5)

        if opening(goal) in context:
            events.append(dummy.copy())

    namespace['q'] = packet
    try:
        sys.setprofile(profile)
        function([0], *header)
    finally:
        sys.setprofile(None)
    return stack + list(reversed(events)) + [header]


if __name__ == '__main__':
    print(json.dumps(translate(json.load(sys.stdin))))
