"""Untrusted global-scope trace compiler for recursive membership tokens.

Input is the old direct-leaf token profile's JSON-lines stream: one goal,
then one three-field packet per line. The output inserts a harmless packet
at each hypothesis leaf. The exact public goal and global numbering stay.
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
    stats = {'source_packets': 0, 'hypothesis_packets': 0}

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

    env['_continue_loop'] = continue_loop
    tree = ast.parse(CONTROL.read_text())
    tree.body = tree.body[:-2]
    fn = next(x for x in tree.body if isinstance(x, ast.FunctionDef) and x.name == 'c')
    loop = next(x for x in fn.body if isinstance(x, ast.While))
    loop.test = ast.Call(func=ast.Name(id='_continue_loop', ctx=ast.Load()),
                         args=[ast.Name(id='a', ctx=ast.Load()), ast.Name(id='g', ctx=ast.Load())],
                         keywords=[])
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
