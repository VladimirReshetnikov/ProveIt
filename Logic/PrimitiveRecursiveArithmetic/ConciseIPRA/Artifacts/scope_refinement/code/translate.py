"""Untrusted certificate compiler; every output must be checked separately.

Input is the strict616 source protocol. Output is an odd-coordinate proof
for the token/AST profiles, or a shared-leaf proof for strict_bytes.py.
This implements the canonical source-proof translation. It diagnoses a
non-leaf retained-computation wrapper instead of silently dropping it.
"""
import argparse
import ast
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def recode(a, depth=0):
    if type(a) is list:
        return [recode(b, depth + 5 - len(a)) for b in a]
    return 1 if type(a) is int and a == 0 and depth % 2 else a


def packet_odd(packet):
    if type(packet) is not list or len(packet) != 4:
        return packet  # permitted unused prefix material
    major, source, seed, template = packet
    return [recode(major), recode(source, 3) if source else source,
            recode(seed, 3) if major or seed else seed,
            recode(template, 0 if major else 3)]


def odd(data):
    return [packet_odd(packet) for packet in data[:-1]] + [recode(data[-1])]


def trace_control(data):
    tree = ast.parse((ROOT / 'controls/prior_strict608.py').read_text())
    namespace = {}
    # This loads the fixed local control, never input text as Python.
    exec(compile(ast.Module(body=tree.body[:2], type_ignores=[]), '<fixed control>', 'exec'), namespace)
    original = namespace['c']
    pending = copy.deepcopy(data)
    root_goal = pending.pop()
    stack, roots = [], []

    def take():
        packet = pending.pop()
        stack[-1]['packet'] = packet
        return packet

    def trace(context, goal, floor=0, phase=0):
        node = dict(goal=goal, context=list(context), floor=floor, children=[])
        (stack[-1]['children'] if stack else roots).append(node)
        stack.append(node)
        try:
            return original(context, goal, floor, phase)
        finally:
            stack.pop()

    namespace.update(c=trace, q=take)
    trace([0], root_goal, phase=1)
    return roots[0]


def opening(a, floor, image=None, depth=0):
    if type(a) is list:
        return [opening(b, floor, image, depth + 5 - len(a)) for b in a]
    if type(a) is int and floor <= a < depth:
        return a or 1
    if depth % 2:
        if image is None:
            raise ValueError('Scope violation')
        return opening(image, floor, depth=3)
    return 0


def computation(packet, floor):
    _, source, seed, template = packet
    return [[source and [source], seed, template],
            opening(template, floor, [source, seed, template], 3) if source else seed]


def compile_node(node):
    if 'packet' not in node:
        return [[0, 0, 0, 0]]
    packet = copy.deepcopy(node['packet'])
    major, source, seed, template = packet
    if not major and not seed and seed != 0:
        packet[2] = 2  # cases marker; scalar zero remains the progress marker
    preview = opening(computation(packet, node['floor']), node['floor'])
    goal = opening(node['goal'], node['floor'])
    if goal == preview:
        return [packet]
    if not major and seed:
        raise ValueError('Non-leaf computation supply: first translate to a canonical derivation')
    result = [packet]
    for child in node['children']:
        result.extend(compile_node(child))
    return result


def shared(data):
    translated = odd(data)
    packets = compile_node(trace_control(translated))
    return packets[::-1] + [translated[-1]]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--profile', choices=('shared', 'odd'), default='shared')
    args = parser.parse_args()
    data = json.load(open(0))
    print(json.dumps(shared(data) if args.profile == 'shared' else odd(data), separators=(',', ':')))
