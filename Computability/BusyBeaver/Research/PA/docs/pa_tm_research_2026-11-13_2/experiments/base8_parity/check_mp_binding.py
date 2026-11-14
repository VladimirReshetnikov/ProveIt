#!/usr/bin/env python3
"""Check the exact MP subtree change; this is not a command-correctness proof."""
from pathlib import Path
import json
import symbolic as S

HERE = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def as_tuple(value):
    return tuple(map(as_tuple, value)) if isinstance(value, list) else value

def paths(tree, needle, path=()):
    if tree == needle:
        yield path
    if tree[0] != 'leaf':
        yield from paths(tree[0], needle, path + (0,))
        yield from paths(tree[1], needle, path + (1,))

def subtree(tree, path):
    for bit in path:
        tree = tree[bit]
    return tree

def substitute(tree, old, new):
    if tree == old:
        return new
    if tree[0] == 'leaf':
        return tree
    return substitute(tree[0], old, new), substitute(tree[1], old, new)

def main():
    original, definitions = S.source_tree()
    changed = as_tuple(json.loads((HERE / 'B8_source_tree.json').read_text()))
    cons8 = substitute(definitions['node65'], definitions['node62'],
                       ((definitions['node61'], definitions['node61']),
                        definitions['node62'][1]))
    occurrences = list(paths(original, definitions['node164']))
    require(occurrences == [(1, 0, 1, 0, 1, 0, 1)], 'unexpected MP occurrence')
    path = occurrences[0]
    expected = substitute(definitions['node164'], definitions['node65'], cons8)
    actual = subtree(changed, path)
    require(actual == expected, 'MP changed beyond the Cons8 replacement')
    require(len(list(paths(actual, cons8))) == 1, 'unexpected MP constructor count')
    old_sites = S.flatten(original)
    new_sites = S.flatten(changed)
    new_indices = {p: i for i, (p, _) in enumerate(new_sites)}
    old_ordinals = [25, 3693, 3707, 3726, 3733, 3754, 3760, 3773, 3799]
    bindings = [{'original_ordinal': i,
                 'path': ''.join(map(str, old_sites[i][0])),
                 'B8_ordinal': new_indices[old_sites[i][0]]}
                for i in old_ordinals]
    result = {'status': 'EXACT_MP_SUBTREE_BINDING_CHECKED',
              'MP_path': ''.join(map(str, path)),
              'MP_only_change': 'Replace its one Cons4 occurrence with Cons8',
              'MP_constructor_occurrences': 1,
              'bindings': bindings,
              'scope': 'Structural source binding only; no new command-level, '
                       'logical-calibration, or blank-start theorem.'}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
