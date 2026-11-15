#!/usr/bin/env python3
"""Deterministically reconstruct PA194GS from the frozen AX11H inputs.

Only Python's standard library and the attributed helpers in vendor/ are used.
The seven contextual folds are frozen witnesses, not the output of a search.
This builder is not a Lean proof checker. See report/report.pdf for the theorem
and its inherited calibration dependency.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'vendor/construction'))
import engine_helpers as b
import compiler as c

EXPECTED = '64ac4ba569b770688a39a1545d5536ad631d15dbb756a0584a8956a83943b3a8'


def build(output, full=False):
    assert __debug__, 'Do not run verification with python -O'
    output.mkdir(parents=True, exist_ok=True)
    inputs = ROOT/'reference/inputs'
    nodes = {k: b.tup(v) for k, v in
             json.loads((inputs/'AX11H.nodes.json').read_text()).items()}
    old_tree = b.grammar(inputs/'AX11H.grammar.json')
    replacements = 0

    def rewrite(t):
        nonlocal replacements
        if not isinstance(t, tuple) or t[0] == 'leaf':
            return t
        if t[1] == ('node150', 'node49'):
            replacements += 1
            return (rewrite(t[0]), ('node146', ('node149', 'node49')))
        return tuple(rewrite(x) for x in t)

    tree = rewrite(old_tree)
    assert replacements == 1
    assert nodes['node150'] == ('node146', 'node149')
    fixed = {k: v for k, v in b.read_table(inputs/'primary.raw.native.tm').items()
             if k[0] < 1300}
    fixed[164, 1] = (1, True, 114)
    for q, bit, action in json.loads((inputs/'h_shift_edits.json').read_text()):
        fixed[q, bit] = tuple(action)
    macros = dict(c.MACROS)
    macros.update({'node146': 196, 'node149': 217})
    del macros['node150']
    inc = ('leaf', 'inc', 1)
    macros[(inc, inc)] = 99
    macros[((inc, inc), (inc, inc))] = 190
    raw, index = dict(fixed), {}

    def entry(t):
        if t in macros:
            return macros[t]
        if t in index:
            return index[t]
        assert len(t) == 2
        q = 2000 + len(index)
        index[t] = q
        for bit, child in enumerate(t):
            raw[q, bit] = (bit, True, entry(child))
        return q

    raw[101, 1] = (1, True, entry(tree))
    raw = b.reachable(raw)
    assert len({q for q, _ in raw if q < 2000}) == 133
    assert len({q for q, _ in raw if q >= 2000}) == 68
    assert len(raw) == 402 and (221, 0) not in raw
    sites, instructions = b.source(nodes, tree)
    old_sites, old_instructions = b.source(nodes, old_tree)
    assert instructions == old_instructions
    assert instructions == json.loads((ROOT/'reference/AX11H/instructions.json').read_text())
    assert len(sites) == 3671
    assert sites[25] == ('1000000', 'dec', 8)
    assert sum(a[0] != z[0] for a, z in zip(sites, old_sites)) == 49
    folds = json.loads((ROOT/'machine/folds.json').read_text())
    assert len(folds) == 7
    child, aliases = b.apply_folds(raw, folds)
    local = b.check_folds(raw, child, aliases, folds)
    assert local['count'] == 28
    assert len(child) == 388 and b.reachable(child) == child
    startup = b.startup(child, sites[25][0])
    assert startup['steps'] == 57922 and startup['complete_tape_equality']
    dense, labels = b.dense(child)
    text = b.table_text(dense)
    actual = hashlib.sha256(text.encode()).hexdigest()
    assert actual == EXPECTED, actual
    result = dict(name='PA194GS', status='PASS', raw_states=201,
                  fixed_states=133, reader_states=68, folds=7, states=194,
                  source_equal=True, source_sites=3671, changed_paths=49,
                  startup=startup, dense_sha256=actual)
    if full:
        import symbolic_runtime as rt
        def frame(i, extra=0, effect=rt.PLAIN):
            return rt.frame(tuple(map(int, sites[i][0])), extra, effect)
        def target(i, extra=0, effect=rt.PLAIN):
            return rt.canonical(frame(i, extra, effect))
        contracts = []
        for i, code in enumerate(instructions):
            initial = frame(i)
            if code[0] == 'inc':
                _, r, n = code
                contracts.append((i, None, initial,
                                  target(n, 0, ('x', 'inc', rt.PHYSICAL[r]))))
            elif code[0] == 'dec':
                _, r, z, n = code
                contracts.extend([
                    (i, (rt.PHYSICAL[r], True), initial, target(z)),
                    (i, (rt.PHYSICAL[r], False), initial,
                     target(n, 1, ('x', 'dec', rt.PHYSICAL[r])))])
            elif code[0] == 'jump':
                contracts.append((i, None, initial, target(code[1])))
            else:
                contracts.append((i, None, initial, None))
        result['runtime'] = rt.validate(child, contracts)
        assert result['runtime']['ok']
    for name, data in [('nodes.json', nodes), ('tree.json', tree),
                       ('sites.json', sites), ('instructions.json', instructions),
                       ('folds.json', folds), ('local_folds.json', local),
                       ('labels.json', labels), ('receipt.json', result)]:
        b.dump(output/name, data)
    for name, rows in [('raw.native.tm', raw), ('machine.native.tm', child),
                       ('machine.tm', dense)]:
        (output/name).write_text(b.table_text(rows))
    print(json.dumps({k: result[k] for k in
                     ('name', 'status', 'states', 'raw_states', 'fixed_states',
                      'reader_states', 'folds', 'source_sites', 'dense_sha256')}))
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'rebuild')
    parser.add_argument('--full', action='store_true',
                        help='also run the compiler-side symbolic search checker')
    args = parser.parse_args()
    build(args.output.resolve(), args.full)
