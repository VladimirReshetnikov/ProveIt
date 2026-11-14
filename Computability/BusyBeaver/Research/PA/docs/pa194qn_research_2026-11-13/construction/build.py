#!/usr/bin/env python3
"""Reconstruct PA194QN and check its source, quotient, and blank seed.

The compiler and symbolic runtime are attributed in NOTICE.txt. This new
builder composes the supplied Q axiom emitter with the supplied N controller.
It does not claim a proof-assistant kernel theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

import compiler as c
import baseline_tools as b

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
INPUT = HERE / 'inputs'
BASE_NODES, BASE_MACHINE = c.raw_nodes, c.machine
EXPECTED_SHA = 'd1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def nodes():
    ns = BASE_NODES()
    assert ns['node163'] == ('node6', 'node55')
    assert ns['node55'] == ('node49', 'node54')
    ns['node163'] = ('node6', 'node54')
    return ns


def machine():
    rows, labels = BASE_MACHINE()
    assert rows[164, 1] == (1, True, 98)
    rows[164, 1] = (1, True, 114)
    return rows, labels


def build(output, full=True):
    assert __debug__ and not sys.flags.optimize, 'Assertions must be enabled.'
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    c.raw_nodes, c.machine = nodes, machine
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    grammar = c.read_grammar(INPUT / 'q.grammar.json')
    original_grammar = c.read_grammar(INPUT / 'primary.grammar.json')
    raw, index, shape = c.build(grammar)
    folds = json.loads((INPUT / 'q.folds.json').read_text())
    child, aliases = b.apply_folds(raw, folds)
    local = b.check_local_folds(raw, child, aliases, folds)
    assert len(raw) == 402 and len(shape) == 67 and len(folds) == 7
    assert len(child) == 388 and len(local['cases']) == 28
    original_rows, _ = BASE_MACHINE()
    assert all(child[q, bit] == original_rows[q, bit]
               for q in c.BOXSTATES for bit in (0, 1))

    sites, instructions, contracts = c.source(grammar)
    old_sites, old_instructions, _ = c.source(original_grammar)
    changes = [i for i in range(len(instructions))
               if instructions[i] != old_instructions[i]]
    assert len(sites) == len(old_sites) == 3654 and len(contracts) == 4755
    assert len(changes) == 79 and min(changes) == 1953 and max(changes) == 2067
    old_word, new_word = b.word(b.expanded(original_grammar)), b.word(b.expanded(grammar))
    assert len(old_word) == len(new_word) == 190
    assert old_word[:102] == new_word[:102] and old_word[121:] == new_word[121:]

    # The N transformation is an exact 19-site splice on the Q-emitter source.
    c.raw_nodes = BASE_NODES
    _, push_instructions, _ = c.source(grammar)
    c.raw_nodes = nodes
    lo, hi = 3634, 3653
    assert len(push_instructions) == 3673
    def relocate(i):
        assert not lo < i < hi
        return i if i <= lo else i - (hi - lo)
    entries = []
    for pc, row in enumerate(push_instructions):
        if lo <= pc < hi:
            continue
        k = 2 if row[0] in ('inc', 'dec') else 1
        for target in row[k:]:
            if lo <= target < hi:
                entries.append([pc, target])
        expected = tuple(row[:k]) + tuple(relocate(v) for v in row[k:])
        assert tuple(instructions[relocate(pc)]) == expected
    assert entries == [[3628, 3634]]

    runtime = c.validate(child, contracts) if full else None
    if full:
        assert runtime['ok'], runtime
    seed = b.startup(child, sites[25][0])
    assert seed['steps'] == 58154
    dense, labels = b.dense_table(child, 194)
    assert sha(b.table_text(dense).encode()) == EXPECTED_SHA
    for filename, table in [('machine.tm', dense), ('machine.native.tm', child),
                            ('raw.native.tm', raw)]:
        (output / filename).write_text(b.table_text(table))
    for filename, value in [
        ('labels.json', labels), ('nodes.json', nodes()), ('folds.json', folds),
        ('local_cases.json', local), ('instructions.json', instructions),
        ('sites.json', [[''.join(map(str, p)), op, a] for p, op, a in sites]),
        ('source.json', dict(sites=sites, instructions=instructions)),
        ('macro_word.json', new_word),
        ('source_comparison.json', dict(changed_from_N=changes,
            changed_instruction_count=79, unchanged_instructions=3575,
            axiom_macro_interval=[102, 121], no_push_removed_interval=[lo, hi],
            sole_external_entry_into_removed_block=entries,
            all_remaining_instructions_match_after_relocation=True))]:
        write_json(output / filename, value)
    receipt = dict(
        status='PASS', family='PA194QN', working_states=194, transition_rows=388,
        native_start=74, native_halt=254, dense_start=0, dense_halt=194,
        raw_states=201, fixed_states=134, AX_readers=67, folds=7,
        simultaneous_fold_cases=28, source_sites=len(sites),
        source_outcomes=len(contracts), source_changed_from_N=79,
        generic_runtime_performed=full, symbolic_runtime=runtime, startup=seed,
        arithmetic_box_rows_unchanged=True, graph_reachable_working_states=194,
        dense_sha256=EXPECTED_SHA,
        native_sha256=sha(b.table_text(child).encode()),
        input_sha256={p.name: sha(p.read_bytes()) for p in sorted(INPUT.iterdir()) if p.is_file()},
        kernel_checked=False,
        scope='Exact construction, source splice and AX change, simultaneous folds, '
              'arbitrary-register source-step contracts, and whole blank-tape startup. '
              'The mathematical command and PA calibration proofs are separate.')
    write_json(output / 'construction_receipt.json', receipt)
    print(json.dumps(receipt, indent=2), flush=True)
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=PACKAGE / 'machine')
    parser.add_argument('--quick', action='store_true', help='Skip only generic physical contracts.')
    args = parser.parse_args()
    build(args.output, full=not args.quick)
