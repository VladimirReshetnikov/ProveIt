#!/usr/bin/env python3
"""Deterministically reconstruct and verify PA194C. Python 3.10+, stdlib only.

The compiler and symbolic block implementation are frozen, attributed copies
from the supplied PA194 packet. This driver composes its decoder with the
six cached-controller rows from supplied 195C, and checks the composition.
Executable certificates support an ordinary proof; no kernel endpoint is claimed.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
REF = ROOT / 'reference/pa194/construction'
sys.path.insert(0, str(REF))
import compiler as c
import build194 as p

EDITS = {(38, 0): (0, True, 11), (38, 1): (1, True, 122),
         (164, 1): (1, True, 130), (214, 0): (0, True, 312),
         (214, 1): (1, True, 20), (312, 0): (0, True, 188)}
EXPECTED = {
    'pa194C.native.tm': 'b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c',
    'pa194C.tm': 'd759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b',
    'pa194C_raw201.native.tm': '46f76f3d0ec9731f13d8887167de17011713780dfb51d7849f40dc468a2aea06',
}

def build(output=None):
    if not __debug__:
        raise SystemExit('Assertions are certificates: do not use Python -O.')
    # Fresh process recommended: the imported compiler has a mutable interface.
    original_machine, original_nodes = c.machine, c.raw_nodes
    original_rows, original_labels = original_machine()
    dense_edits = {(115, 1): (1, True, 108), (37, 0): (0, True, 11),
                   (37, 1): (1, True, 101), (127, 0): (0, True, 133),
                   (127, 1): (1, True, 20), (133, 0): (0, True, 120)}
    assert EDITS == {(original_labels[q], b): (w, d, original_labels[n])
                     for (q, b), (w, d, n) in dense_edits.items()}

    def machine():
        rows, labels = original_machine()
        rows.update(EDITS)
        return rows, labels

    def nodes():
        result = original_nodes()
        result['node163'] = ('node6', 'node147')
        result['node170'] = (('node36', ('node167', 'node145')), 'node57')
        return result

    c.machine, c.raw_nodes = machine, nodes
    c.PHYSICAL[:] = [6, 2, 0, 4, 3, 7, 8, 5, 1]
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    grammar = c.read_grammar(ROOT / 'source/grammar.json')
    old_grammar = c.read_grammar(REF / 'inputs/parent195S.grammar.json')
    assert p.word(p.expanded(grammar)) == p.word(p.expanded(old_grammar))
    assert len(p.word(p.expanded(grammar))) == 190

    sites, instructions, contracts = c.source(grammar)
    old_sites, old_instructions, _ = c.source(old_grammar)
    assert instructions == old_instructions
    assert [(op, arg) for _, op, arg in sites] == [(op, arg) for _, op, arg in old_sites]
    assert json.loads(json.dumps(instructions)) == json.loads(
        (ROOT / 'reference/cached/parent195C.source.instructions.json').read_text())
    assert len(sites) == 3649 and len(contracts) == 4749

    raw, index, shape = c.build(grammar)
    old_raw, _, old_shape = c.build(old_grammar)
    assert len(shape) == len(old_shape) == 67
    assert len(raw) == 402 and len({q for q, _ in raw if q < 1300}) == 134
    assert {k: a for k, a in raw.items() if k[0] < 1300} == {
        k: a for k, a in old_raw.items() if k[0] < 1300}
    folds = json.loads((ROOT / 'source/folds.json').read_text())
    old_folds = json.loads((REF / 'inputs/parent195S.folds.json').read_text())
    child, aliases = p.apply_folds(raw, folds)
    parent, old_aliases = p.apply_folds(old_raw, old_folds)
    assert len(folds) == 7 and len(old_folds) == 6
    assert parent == p.read_table(ROOT / 'reference/cached/parent195C.machine.native.tm')
    local = p.check_local_folds(raw, child, aliases, folds)
    assert len(local['cases']) == 28 and len(local['incoming_rows']) == 23
    assert all(child[q, b] == original_rows[q, b] for q in c.BOXSTATES for b in (0, 1))
    primary = p.read_table(REF / 'tables/pa194.native.tm')
    assert {key for key in child if child[key] != primary[key]} == set(EDITS)
    dense, labels = p.dense_table(child)
    files = {'pa194C.native.tm': p.table_text(child), 'pa194C.tm': p.table_text(dense),
             'pa194C_raw201.native.tm': p.table_text(raw)}
    for name, content in files.items():
        assert hashlib.sha256(content.encode()).hexdigest() == EXPECTED[name]
        assert (ROOT / 'tables' / name).read_text() == content
    assert json.loads((ROOT / 'tables/pa194C.labels.json').read_text()) == labels
    site_data = [[''.join(map(str, path)), op, arg] for path, op, arg in sites]
    assert site_data == json.loads((ROOT / 'source/pa194C.sites.json').read_text())
    assert json.loads(json.dumps(instructions)) == json.loads(
        (ROOT / 'source/pa194C.instructions.json').read_text())
    startup = p.startup(child, sites[25][0])
    assert startup['steps'] == 57922
    validation = c.validate(child, contracts)
    assert validation == {'ok': True, 'contracts': 4749, 'max_steps': 506, 'total_steps': 1507397}
    receipt = {'family': 'PA194C', 'working_states': 194, 'transition_rows': 388,
               'fixed_controls': 134, 'raw_readers': 67, 'folds': 7,
               'source_sites': 3649, 'source_outcomes': 4749,
               'source_graph_equal_to_195C': True, 'parent195C_reproduced_exactly': True,
               'arithmetic_boxes_unchanged': True, 'local_cases': 28, 'incoming_rows': 23,
               'maximum_local_duration': max(x['duration'] for x in local['cases']),
               'changed_rows': [[q, b, *a] for (q, b), a in sorted(EDITS.items())],
               'startup': startup, 'symbolic': validation, 'sha256': EXPECTED,
               'kernel_checked': False}
    if output:
        output = Path(output)
        output.mkdir(parents=True, exist_ok=True)
        for name, content in files.items(): (output / name).write_text(content)
        (output / 'construction.json').write_text(json.dumps(receipt, indent=2) + '\n')
        (output / 'local_folds.json').write_text(json.dumps(local, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
    return receipt

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional fresh evidence/output directory.')
    build(parser.parse_args().output)
