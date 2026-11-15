#!/usr/bin/env python3
"""Deterministic, offline construction of PA194AX11GH and PA194AX11GHS.

Imported compiler and arithmetic-box checker are explicitly attributed in
PROVENANCE.json. Independent literal and source-template checkers are separate.
Outputs go to a new directory, never over the frozen delivered certificates.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
sys.path.insert(0, str(HERE / 'vendor'))
import compiler as c
import support as s

NAMES = ('PA194AX11GH', 'PA194AX11GHS')
EXPECTED = {
    NAMES[0]: ('513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1',
               3671, 4778, 57922, 1518827),
    NAMES[1]: ('7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c',
               3668, 4774, 57768, 1525009),
}


def tup(value):
    return tuple(map(tup, value)) if isinstance(value, list) else value


def build(name, output, full=True):
    assert __debug__ and not sys.flags.optimize, 'Run with assertions enabled.'
    inputs = HERE / 'inputs'
    delivered = PACKAGE / 'machines' / name
    digest, site_count, outcome_count, startup_steps, symbolic_steps = EXPECTED[name]
    raw_parent = s.read_table(inputs / 'AX11G.raw.native.tm')
    parent_nodes = {k: tup(v) for k, v in json.loads(
        (inputs / 'AX11G.nodes.json').read_text()).items()}
    grammar = tup(json.loads((inputs / 'AX11G.grammar.tree.json').read_text()))
    folds = json.loads((inputs / 'AX11G.folds.json').read_text())
    assert len(raw_parent) == 402 and len(folds) == 7
    assert parent_nodes['node170'] == ('node36', 'node169')
    raw = dict(raw_parent)
    edits = {(38, 0): (0, True, 11), (38, 1): (1, True, 122),
             (214, 0): (0, True, 312), (214, 1): (1, True, 20),
             (312, 0): (0, True, 188)}
    raw.update(edits)
    nodes = dict(parent_nodes)
    nodes['node170'] = (('node36', ('node167', 'node145')), 'node57')
    if name == NAMES[1]:
        extra = {(214, 1): (1, True, 30), (310, 1): (1, True, 330),
                 (330, 0): (0, True, 63), (330, 1): (1, False, 73)}
        raw.update(extra)
        edits.update(extra)
        nodes['node170'] = (('node36', ('node167', 'node145')), 'node56')
        nodes['node171'] = ('node170', (('leaf', 'inc', 5), ('leaf', 'continueTo', 3)))
        folds += [[41, 330, [[0, False, 31], [1, False, 46]]]]
    c.machine = lambda: (raw, [])
    c.raw_nodes = lambda: nodes
    c.PHYSICAL[:] = [6, 2, 0, 4, 3, 7, 8, 5, 1]
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    rebuilt, _, shape = c.build(grammar)
    assert rebuilt == raw and len(shape) == 67
    # Retain the compiler's deterministic insertion order for the incoming-row
    # list in the fold certificate; equality above checks every transition.
    raw = rebuilt
    rows, aliases = s.apply_folds(raw, folds)
    cases = s.check_local_folds(raw, rows, aliases, folds)
    assert len(cases['cases']) == 4 * len(folds)
    assert all(rows[q, b] == raw_parent[q, b] for q in c.BOXSTATES for b in (0, 1))
    sites, instructions, contracts = c.source(grammar)
    assert len(sites) == site_count and len(contracts) == outcome_count
    runtime = c.validate(rows, contracts) if full else None
    if full:
        assert runtime == {'ok': True, 'contracts': outcome_count,
                           'max_steps': 479, 'total_steps': symbolic_steps}
    startup = s.startup(rows, sites[25][0])
    assert startup['steps'] == startup_steps
    dense, labels = s.dense_table(rows, 194)
    assert hashlib.sha256(s.table_text(dense).encode()).hexdigest() == digest
    payloads = {'labels.json': labels, 'nodes.json': nodes,
                'grammar.tree.json': grammar, 'folds.json': folds,
                'fold_cases.json': cases,
                'sites.json': [[''.join(map(str, p)), op, a] for p, op, a in sites],
                'instructions.json': instructions}
    for filename, value in payloads.items():
        assert json.loads((delivered / filename).read_text()) == json.loads(json.dumps(value)), filename
    output.mkdir(parents=True, exist_ok=True)
    for filename, table in [('machine.tm', dense), ('machine.native.tm', rows),
                            ('raw.native.tm', raw)]:
        text = s.table_text(table)
        assert text == (delivered / filename).read_text(), filename
        (output / filename).write_text(text)
    for filename, value in payloads.items():
        (output / filename).write_text(json.dumps(value, indent=2) + '\n')
    receipt = dict(name=name, status='PASS', working_states=194, transitions=388,
                   raw_fixed_states=len(raw)//2-len(shape), raw_reader_states=len(shape),
                   simultaneous_folds=len(folds), local_fold_cases=4*len(folds),
                   source_sites=site_count, source_outcomes=outcome_count,
                   runtime=runtime, universal_construction_replay_performed=full,
                   startup=startup, dense_sha256=digest,
                   arithmetic_box_rows_unchanged=True, kernel_checked=False,
                   scope='Deterministic literal construction, simultaneous folds, exact source identity, '
                         'whole blank startup and optional inherited-box symbolic contracts. '
                         'Independent literal induction and logical calibration are separate checks.')
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--machine', choices=NAMES)
    parser.add_argument('--quick', action='store_true', help='Explicitly skip construction symbolic contracts.')
    args = parser.parse_args()
    output = args.output or Path(tempfile.mkdtemp(prefix='pa194-ax11gh-build-'))
    for name in ([args.machine] if args.machine else NAMES):
        receipt = build(name, output / name, not args.quick)
        print(json.dumps({k: receipt[k] for k in ('name', 'status', 'working_states',
              'source_sites', 'source_outcomes', 'dense_sha256')}, sort_keys=True), flush=True)
    print('output:', output)
