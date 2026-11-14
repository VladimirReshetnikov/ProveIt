#!/usr/bin/env python3
"""Rebuild PA194NQ and check the two disjoint source modifications.

The arithmetic blocks and binary-tree compiler are attributed in NOTICE.txt.
This executable certificate supports an ordinary mathematical PA proof; it is
not a Lean/Rocq proof-assistant theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import compiler as c
import baseline_tools as b

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
EXPECTED = 'd1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231'
ORIGINAL_NODES, ORIGINAL_MACHINE = c.raw_nodes, c.machine


def save_json(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def new_nodes():
    nodes = ORIGINAL_NODES()
    assert nodes['node163'] == ('node6', 'node55')
    assert nodes['node55'] == ('node49', 'node54')
    nodes['node163'] = ('node6', 'node54')
    return nodes


def new_machine():
    rows, labels = ORIGINAL_MACHINE()
    assert rows[164, 1] == (1, True, 98)
    rows[164, 1] = (1, True, 114)
    return rows, labels


def build(output, validate=True):
    if not __debug__:
        raise RuntimeError('Run without Python -O or PYTHONOPTIMIZE.')
    output.mkdir(parents=True, exist_ok=True)
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    original = c.read_grammar(HERE/'inputs/pa194.grammar.json')
    exchanged = c.read_grammar(HERE/'inputs/q.grammar.json')
    old_word, new_word = b.word(b.expanded(original)), b.word(b.expanded(exchanged))
    assert len(old_word) == len(new_word) == 190
    assert old_word[:102] == new_word[:102]
    assert old_word[121:] == new_word[121:]

    c.raw_nodes, c.machine = ORIGINAL_NODES, ORIGINAL_MACHINE
    base_sites, base_instructions, _ = c.source(original)
    old_q_sites, old_q_instructions, _ = c.source(exchanged)
    c.raw_nodes, c.machine = new_nodes, new_machine
    n_sites, n_instructions, _ = c.source(original)
    sites, instructions, contracts = c.source(exchanged)
    assert len(base_sites) == len(old_q_sites) == 3673
    assert len(n_sites) == len(sites) == 3654
    assert len(contracts) == 4755
    changes = [i for i, (old, new) in enumerate(zip(n_instructions, instructions)) if old != new]
    assert len(changes) == 79
    # The N splice is the same exact 19-site deletion on either emitter.
    lo, hi = 3634, 3653
    def relocated(index):
        assert not lo < index < hi
        return index if index <= lo else index - (hi-lo)
    def splice_check(old, new):
        incoming = []
        for pc, row in enumerate(old):
            if lo <= pc < hi:
                continue
            prefix = 2 if row[0] in ('inc', 'dec') else 1
            if row[0] != 'halt':
                incoming += [[pc, target] for target in row[prefix:] if lo <= target < hi]
            assert new[relocated(pc)] == row[:prefix] + tuple(relocated(x) for x in row[prefix:])
        assert incoming == [[3628, 3634]]
        return incoming
    entry1 = splice_check(base_instructions, n_instructions)
    entry2 = splice_check(old_q_instructions, instructions)
    assert entry1 == entry2

    raw, _, shape = c.build(exchanged)
    folds = json.loads((HERE/'inputs/q.folds.json').read_text())
    child, aliases = b.apply_folds(raw, folds)
    local = b.check_local_folds(raw, child, aliases, folds)
    assert len(raw) == 402 and len(shape) == 67 and len(folds) == 7
    assert len(child) == 388 and len(local['cases']) == 28
    upstream, _ = ORIGINAL_MACHINE()
    assert all(child[q, bit] == upstream[q, bit] for q in c.BOXSTATES for bit in (0, 1))
    validation = c.validate(child, contracts) if validate else None
    assert not validate or validation['ok']
    startup = b.startup(child, sites[25][0])
    assert startup['steps'] == 58154
    dense, labels = b.dense_table(child, 194)
    dense_bytes = b.table_text(dense).encode()
    assert hashlib.sha256(dense_bytes).hexdigest() == EXPECTED
    for name, table in [('machine.tm', dense), ('machine.native.tm', child), ('raw.native.tm', raw)]:
        (output/name).write_text(b.table_text(table))
    for name, value in [('labels.json', labels), ('instructions.json', instructions),
                        ('sites.json', [[''.join(map(str,p)),op,a] for p,op,a in sites]),
                        ('nodes.json', new_nodes()), ('local_folds.json', local),
                        ('macro_word.json', new_word)]:
        save_json(output/name, value)
    receipt = {'name': 'PA194NQ', 'states': 194, 'transition_rows': 388,
               'start': 0, 'halt': 194, 'native_start': 74, 'native_halt': 254,
               'fixed_controls': 134, 'raw_readers': 67, 'folds': 7,
               'source_sites': len(sites), 'contracts': len(contracts),
               'changed_instructions_from_N': len(changes),
               'exchange_instruction_indices': changes,
               'deleted_source_interval': [lo,hi],
               'unique_entry_into_deleted_interval': entry1,
               'source_modifications_commute': True,
               'macro_tokens': 190, 'exchanged_word_interval': [102,121],
               'symbolic_validation': validation, 'seed': startup,
               'sha256': EXPECTED, 'kernel_checked': False}
    save_json(output/'receipt.json', receipt)
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('seed','exchange_instruction_indices')}, indent=2))
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=PACKAGE/'machine')
    parser.add_argument('--quick', action='store_true', help='Skip only the first symbolic runtime replay.')
    args = parser.parse_args()
    build(args.output, not args.quick)
