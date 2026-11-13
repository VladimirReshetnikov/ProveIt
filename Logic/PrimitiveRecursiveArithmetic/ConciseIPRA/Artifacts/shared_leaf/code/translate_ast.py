"""Untrusted canonical global trace compiler for star_context_ast.py.

The source is direct-leaf token243. At each hypothesis leaf insert [0,0,0].
At each zero-source introduction also insert [0,0,0] for the new explicit
neutral-major proof. The candidate is always executed independently.
"""
import ast
import copy
import json
from pathlib import Path
import sys

CONTROL = Path(__file__).resolve().parents[1] / 'controls/checker_tokens.py'


def convert(lines):
    values = [json.loads(x) for x in lines.splitlines() if x.strip()]
    goal, pending = values[0], iter(values[1:])
    emitted = []
    stats = {'source_packets': 0, 'hypothesis_packets': 0, 'neutral_major_packets': 0}

    def read_packet():
        packet = next(pending)
        emitted.append(copy.deepcopy(packet))
        stats['source_packets'] += 1
        return json.dumps(packet)

    env = {'input': read_packet}

    def continue_loop(a, g):
        if env['i'](a) in g:
            emitted.append([0, 0, 0])
            stats['hypothesis_packets'] += 1
            return False
        return True

    def neutral():
        emitted.append([0, 0, 0])
        stats['neutral_major_packets'] += 1

    env.update(_continue_loop=continue_loop, _neutral=neutral)
    tree = ast.parse(CONTROL.read_text())
    tree.body = tree.body[:-2]
    fn = next(x for x in tree.body if isinstance(x, ast.FunctionDef) and x.name == 'c')
    loop = next(x for x in fn.body if isinstance(x, ast.While))
    loop.test = ast.Call(func=ast.Name(id='_continue_loop', ctx=ast.Load()),
                         args=[ast.Name(id='a', ctx=ast.Load()), ast.Name(id='g', ctx=ast.Load())],
                         keywords=[])
    assignment = next(x for x in loop.body if isinstance(x, ast.Assign)
                      and isinstance(x.targets[0], ast.Name) and x.targets[0].id == 'h')
    branch = assignment.value
    if not isinstance(branch, ast.IfExp):
        raise ValueError('unrecognized source protocol')
    branch.orelse = ast.Subscript(
        value=ast.Tuple(elts=[ast.Call(func=ast.Name(id='_neutral', ctx=ast.Load()), args=[], keywords=[]),
                              branch.orelse], ctx=ast.Load()),
        slice=ast.Constant(value=1), ctx=ast.Load())
    ast.fix_missing_locations(tree)
    exec(compile(tree, str(CONTROL), 'exec'), env)
    env['c'](goal)
    stats['new_packets'] = len(emitted)
    return '\n'.join(json.dumps(x, separators=(',', ':')) for x in [goal] + emitted) + '\n', stats


if __name__ == '__main__':
    source, target = map(Path, sys.argv[1:])
    result, stats = convert(source.read_text())
    target.write_text(result)
    print(json.dumps(stats, sort_keys=True))
