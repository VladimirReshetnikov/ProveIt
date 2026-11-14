#!/usr/bin/env python3
"""Rebuild and check the 195-state AX reassociation, using only Python's stdlib.

The default uses the supplied separate-Gamma calculus and the original PA196
fixed controller.  --combined selects the separately documented Combined196
outer-controller/source variant.  Neither mode changes the AX macro word.

This is an executable finite certificate checker, not a Lean proof.  Its
symbolic register oracle uses the unchanged arithmetic-box contracts described
in reference/M6/Runtime.lean.
"""
from pathlib import Path
import argparse
import hashlib
import json

import compiler as c
from support import apply, localvalid
from verify_emitter import word
import supplied_verify

HERE = Path(__file__).resolve().parent
START = 74
HALT = 254


def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))


def expanded(t):
    inc = ('leaf', 'inc', 1)
    if t == 'node60':
        return (inc, inc)
    if t == 'node61':
        return ((inc, inc), (inc, inc))
    return tuple(expanded(x) for x in t) if c.isnode(t) else t


def enable_combined():
    old_machine, old_raw = c.machine, c.raw_nodes
    _, labels = old_machine()
    # The exact six transitions in dense PA196 coordinates.
    changes = {
        (115, 1): (1, True, 108),
        (37, 0): (0, True, 11),
        (37, 1): (1, True, 101),
        (127, 0): (0, True, 133),
        (127, 1): (1, True, 20),
        (133, 0): (0, True, 120),
    }
    edits = {(labels[q], b): (w, d, labels[n])
             for (q, b), (w, d, n) in changes.items()}

    def machine():
        rows, lab = old_machine()
        rows.update(edits)
        return rows, lab

    def raw_nodes():
        nodes = old_raw()
        nodes['node163'] = ('node6', 'node147')
        nodes['node170'] = (('node36', ('node167', 'node145')), 'node57')
        return nodes

    c.machine, c.raw_nodes = machine, raw_nodes
    return [[q, b, w, d, n] for (q, b), (w, d, n) in sorted(edits.items())]


def startup(rows, path, bound=100000):
    """Exact finite tape equality, not just arrival at a control state."""
    expected_head = -2
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {expected_head - 1, expected_head + 48}
    expected |= {expected_head + i for i, b in enumerate(path) if b}
    pos = expected_head + 49
    for v in physical:
        pos += 1
        expected.update(range(pos, pos + v + 1))
        pos += v + 1
    tape, q, head = set(), START, 0
    for step in range(1, bound + 1):
        w, d, q = rows[q, int(head in tape)]
        (tape.add if w else tape.discard)(head)
        head += 1 if d else -1
        if q == 84 and head == expected_head and tape == expected:
            return step
        if q == HALT:
            raise AssertionError(f'Unexpected blank-tape halt at step {step}')
    raise AssertionError(f'Clean source entry not reached within {bound} steps')


def rooted_graph(rows):
    """BFS relabeling is canonical for a pointed, 0/1-edge-labelled graph."""
    order, index = [START], {START: 0}
    for q in order:
        for b in (0, 1):
            n = rows[q, b][2]
            if n != HALT and n not in index:
                index[n] = len(order)
                order.append(n)
    assert len(order) == 195
    dense = {(index[q], b): (w, d, 195 if n == HALT else index[n])
             for (q, b), (w, d, n) in rows.items()}
    return order, dense


def main():
    if not __debug__:
        raise SystemExit('Run without Python -O: the parser and certificate assertions are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--combined', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    # Bind the source used for the endpoint comparison to the exact published
    # parent table, with the supplied folds and supplied dense conjugacy.
    assert (HERE / 'baseline.grammar.json').read_bytes() == (
        HERE / 'separate196/grammar.json').read_bytes()
    parent_receipt = supplied_verify.check('separate196')
    changes = enable_combined() if args.combined else []
    family = '195C' if args.combined else '195S'
    out = args.output or HERE / ('rebuilt_' + family)
    out.mkdir(parents=True, exist_ok=True)
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    grammar = c.read_grammar(HERE / 'grammar.json')
    baseline = c.read_grammar(HERE / 'baseline.grammar.json')
    assert word(expanded(grammar)) == word(expanded(baseline))
    assert len(word(expanded(grammar))) == 190
    sites, instructions, contracts = c.source(grammar)
    old_sites, old_instructions, _ = c.source(baseline)
    assert [(op, arg) for _, op, arg in sites] == [
        (op, arg) for _, op, arg in old_sites]
    assert instructions == old_instructions
    rows, index, shape = c.build(grammar)
    assert len(shape) == 67 and len(rows) == 2 * 201
    parent_rows, _, parent_shape = c.build(baseline)
    assert len(parent_shape) == 68
    fixed_rows = {key: value for key, value in rows.items() if key[0] < 1300}
    assert len(fixed_rows) == 2 * 134
    assert fixed_rows == {key: value for key, value in parent_rows.items()
                          if key[0] < 1300}
    folds = json.loads((HERE / 'folds.json').read_text())
    assert len(folds) == 6
    assert len({q for a, b, actions in folds for q in (a, b)}) == 12
    incoming = {q: set() for q in shape}
    for (q, bit), (w, d, target) in rows.items():
        if target in shape:
            assert w == bit and d
            incoming[target].add(bit)
    for a, b, actions in folds:
        assert incoming[a] == {0} and incoming[b] == {1}
    folded, aliases = apply(rows, folds)
    assert localvalid(rows, folded, aliases, folds)
    assert len(folded) == 2 * 195
    states = {q for q, b in folded}
    assert all((q, b) in folded for q in states for b in (0, 1))
    assert {n for w, d, n in folded.values()} - states == {HALT}
    baseline_rows, _ = c.machine()
    oracle_box_states_unchanged = all(
        folded[q, b] == baseline_rows[q, b]
        for q in c.BOXSTATES for b in (0, 1))
    assert oracle_box_states_unchanged
    valid = c.validate(folded, contracts)
    assert valid['ok'], valid
    startup_steps = startup(folded, sites[25][0])
    order, dense = rooted_graph(folded)
    native = table_text(folded)
    dense_text = table_text(dense)
    (out / 'machine.native.tm').write_text(native)
    (out / 'machine.dense.tm').write_text(dense_text)
    (out / 'dense_to_native.json').write_text(json.dumps(order + [HALT]) + '\n')
    (out / 'source.instructions.json').write_text(json.dumps(instructions, indent=2) + '\n')
    (out / 'source.sites.json').write_text(json.dumps([
        [''.join(map(str, p)), op, arg] for p, op, arg in sites]) + '\n')
    receipt = {
        'family': family,
        'working_states': 195,
        'graph_reachable_working_states': len(order),
        'native_start': START,
        'native_halt': HALT,
        'dense_start': 0,
        'dense_halt': 195,
        'fixed_states': 134,
        'raw_reader_states': len(shape),
        'simultaneous_folds': len(folds),
        'fixed_controller_equal_to_parent_compilation': True,
        'fold_entry_contexts_exact': True,
        'macro_word_equal': True,
        'macro_tokens': 190,
        'source_opcode_argument_sequence_equal': True,
        'resolved_instruction_map_equal': True,
        'source_sites': len(sites),
        'unchanged_symbolic_oracle_boxes': oracle_box_states_unchanged,
        'local_fold_valid': True,
        'symbolic_validation': valid,
        'blank_startup_steps': startup_steps,
        'native_table_sha256': hashlib.sha256(native.encode()).hexdigest(),
        'dense_table_sha256': hashlib.sha256(dense_text.encode()).hexdigest(),
        'combined_edits': changes,
        'literal_parent_reproduction': parent_receipt,
    }
    (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
