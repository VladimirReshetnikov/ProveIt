#!/usr/bin/env python3
"""Reconstruct PA194AX11H / PA194QAX11H and check source contracts.

Python 3.10+, standard library. Run with assertions enabled. This builds
literal tables and executable certificates, not an end-to-end iPRA proof.
The imported compiler and symbolic engine are attributed in NOTICE.md.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'construction'))
import compiler as c
import support


def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def flattened(t):
    return flattened(t[0]) + flattened(t[1]) if c.isnode(t) else [t]


def push_exit(t):
    if t == c.BREAK:
        return 'node49'
    return tuple(map(push_exit, t)) if c.isnode(t) else t


def grammar_json(t):
    names, rules = {}, {}
    def visit(v):
        if not c.isnode(v):
            return v
        if v in names:
            return names[v]
        name = 'g' + str(len(names))
        names[v] = name
        rules[name] = [visit(v[0]), visit(v[1])]
        return name
    root = visit(t)
    return dict(root=root, rules=rules)


def check_inputs():
    expected = json.loads((ROOT / 'inputs' / 'sha256.json').read_text())
    for name, digest in expected.items():
        assert hashlib.sha256((ROOT / 'inputs' / name).read_bytes()).hexdigest() == digest, name


def build(family, out, full=True):
    assert __debug__ and not sys.flags.optimize, 'Do not use Python -O.'
    assert family in ('PA194AX11H', 'PA194QAX11H')
    check_inputs()
    expected = json.loads((ROOT / 'expected.json').read_text())[family]
    inp = ROOT / 'inputs'
    original = support.read_table(inp / 'primary.raw.native.tm')
    nodes = {k: tup(v) for k, v in json.loads((inp / 'primary.nodes.json').read_text()).items()}
    c.machine = lambda: (original, [])
    c.raw_nodes = lambda: nodes
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190

    old = c.read_grammar(inp / 'primary.grammar.json')
    old_sites, old_ins, _ = c.source(old)
    assert json.loads(json.dumps(old_ins)) == json.loads((inp / 'primary.instructions.json').read_text())
    assert [[''.join(map(str, p)), op, a] for p, op, a in old_sites] == json.loads((inp / 'primary.sites.json').read_text())
    assert nodes['node163'] == ('node6', 'node55')
    assert nodes['node170'] == ('node36', 'node169')

    # Visible/no-push MP and cached-head-only Shift.
    nodes['node163'] = ('node6', 'node54')
    nodes['node170'] = (('node36', ('node167', 'node145')), 'node57')
    fixed = dict(original)
    fixed[164, 1] = (1, True, 114)
    for q, bit, action in json.loads((inp / 'h_shift_edits.json').read_text()):
        fixed[q, bit] = tuple(action)
    c.machine = lambda: (fixed, [])

    prefix = 'q' if family == 'PA194QAX11H' else 'primary'
    old_grammar = c.read_grammar(inp / (prefix + '.grammar.json'))
    word = flattened(old_grammar)
    assert word[-1] == c.BREAK and word.count(c.BREAK) == 1
    grammar = push_exit(old_grammar)
    assert flattened(grammar) == word[:-1] + ['node49']
    raw, index, shape = c.build(grammar)
    folds = json.loads((inp / (prefix + '.folds.json')).read_text())
    rows, aliases = support.apply_folds(raw, folds)
    local = support.check_local_folds(raw, rows, aliases, folds)
    assert len(raw) == 402 and len(shape) == 67 and len(folds) == 7
    assert len(local['cases']) == 28
    assert all(raw[q, bit] == original[q, bit] for q in c.BOXSTATES for bit in (0, 1))

    sites, instructions, contracts = c.source(grammar)
    assert len(sites) == expected['sites'] == 3671
    assert len(contracts) == expected['contracts'] == 4778
    runtime = c.validate(rows, contracts) if full else None
    if full:
        assert runtime['ok'] and runtime['contracts'] == 4778, runtime
    startup = support.startup(rows, sites[25][0])
    assert startup['steps'] == expected['startup'] == 57922
    dense, labels = support.dense_table(rows, 194)
    text = support.table_text(dense)
    digest = hashlib.sha256(text.encode()).hexdigest()
    assert digest == expected['dense_sha256']
    out.mkdir(parents=True, exist_ok=True)
    for name, table in [('machine.tm', dense), ('machine.native.tm', rows), ('raw.native.tm', raw)]:
        (out / name).write_text(support.table_text(table))
    for name, value in [
        ('labels.json', labels), ('nodes.json', nodes),
        ('grammar.tree.json', grammar), ('grammar.json', grammar_json(grammar)),
        ('sites.json', [[''.join(map(str, p)), op, a] for p, op, a in sites]),
        ('instructions.json', instructions), ('folds.json', folds), ('local_folds.json', local),
    ]:
        dump(out / name, value)
    receipt = dict(
        family=family, working_states=194, transition_rows=388,
        raw_controls=201, fixed_controls=134, raw_reader_controls=67, folds=7,
        dense_start=0, dense_halt=194, native_start=74, native_halt=254,
        source_sites=len(sites), source_contracts=len(contracts), runtime=runtime,
        local_fold_cases=len(local['cases']),
        maximum_local_fold_duration=max(x['duration'] for x in local['cases']),
        startup=startup, arithmetic_box_rows_unchanged=True,
        dense_sha256=digest,
        native_sha256=hashlib.sha256(support.table_text(rows).encode()).hexdigest(),
        full_construction_replay=full, kernel_checked=False,
        arithmetic_derivation_checked_by_this_script=False,
    )
    dump(out / 'receipt.json', receipt)
    print(json.dumps({k: receipt[k] for k in ('family','working_states','source_sites','source_contracts','runtime','dense_sha256')}, indent=2), flush=True)
    return receipt


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family', choices=['PA194AX11H', 'PA194QAX11H'], default='PA194AX11H')
    p.add_argument('--output', type=Path)
    p.add_argument('--quick', action='store_true', help='Skip construction symbolic replay; recorded as such.')
    args = p.parse_args()
    build(args.family, args.output or Path(tempfile.mkdtemp(prefix='pa194-ax11h-')), not args.quick)
