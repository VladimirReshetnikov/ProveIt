#!/usr/bin/env python3
"""Reconstruct and verify the 194-state separated-head PA machine.

Python 3.10+, standard library only; run without -O. No search, network,
repository checkout, or proof assistant is required. The symbolic executor
uses the unchanged arithmetic-block lemmas in reference/M6/Runtime.lean.
The separate independent physical audit in the release checks those blocks
from literal rows. These executable certificates are not a new Lean proof.
"""
from pathlib import Path
import argparse
import hashlib
import json

import compiler as c

HERE = Path(__file__).resolve().parent
START, HALT = 74, 254
ORIGINAL_PHYSICAL = [6, 2, 0, 4, 3, 7, 8, 5, 1]
ORIGINAL_MACHINE, ORIGINAL_NODES = c.machine, c.raw_nodes
EXPECTED_NATIVE = 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
EXPECTED_DENSE = '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'


def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))


def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in result
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        result[q, b] = w, d == 'R', n
    return result


def expanded(t):
    inc = ('leaf', 'inc', 1)
    if t == 'node60':
        return inc, inc
    if t == 'node61':
        return (inc, inc), (inc, inc)
    return tuple(map(expanded, t)) if c.isnode(t) else t


def word(t):
    return word(t[0]) + word(t[1]) if c.isnode(t) else [t]


def apply_folds(rows, folds):
    aliases = {a: b for a, b, actions in folds}
    actions = {b: acts for a, b, acts in folds}
    assert len(aliases) == len(folds)
    assert len({q for a, b, acts in folds for q in (a, b)}) == 2 * len(folds)
    out = {}
    for (q, bit), act in rows.items():
        if q in aliases:
            continue
        w, d, target = actions[q][bit] if q in actions else act
        out[q, bit] = w, bool(d), aliases.get(target, target)
    return out, aliases


def check_local_folds(raw, folded, aliases, folds):
    """Exhaust all four contexts per pair on the final simultaneous table."""
    incoming = {}
    for (q, bit), (w, d, target) in raw.items():
        incoming.setdefault(target, []).append([q, bit, w, d, target])
    cases = []
    for a, b, acts in folds:
        assert START not in (a, b)
        assert {(row[2], row[3]) for row in incoming[a]} == {(0, True)}
        assert {(row[2], row[3]) for row in incoming[b]} == {(1, True)}
        for old, history in ((a, 0), (b, 1)):
            for bit in (0, 1):
                w, d, target = raw[old, bit]
                expected = (aliases.get(target, target), 1 if d else -1,
                            {-1: history, 0: w})
                now, pos, tape = b, 0, {-1: history, 0: bit}
                trace = [[now, pos, tape[-1], tape[0]]]
                for steps in range(1, 21):
                    assert pos in (-1, 0)
                    wr, dr, now = folded[now, tape[pos]]
                    tape[pos] = wr
                    pos += 1 if dr else -1
                    trace.append([now, pos, tape[-1], tape[0]])
                    if (now, pos, tape) == expected:
                        break
                else:
                    raise AssertionError(('local simulation did not close', old, bit))
                cases.append({'old_state': old, 'history_bit': history,
                              'current_bit': bit, 'duration': steps, 'trace': trace})
    affected = {q for a, b, acts in folds for q in (a, b)}
    return {'cases': cases, 'incoming_rows': [row for q in sorted(affected)
                                            for row in incoming[q]]}


def dense_table(rows, count=194):
    controls = {q for q, bit in rows}
    assert len(controls) == count and len(rows) == 2 * count and HALT not in controls
    assert all((q, bit) in rows for q in controls for bit in (0, 1))
    assert {n for w, d, n in rows.values()} - controls == {HALT}
    order, index = [START], {START: 0}
    for q in order:
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target != HALT and target not in index:
                index[target] = len(order)
                order.append(target)
    assert len(order) == count
    dense = {(index[q], bit): (w, d, count if n == HALT else index[n])
             for (q, bit), (w, d, n) in rows.items()}
    return dense, order + [HALT]


def startup(rows, path):
    """Check the complete finite-support tape, head, and clean source frame."""
    expected_head = -2
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {expected_head - 1, expected_head + 48}
    expected.update(expected_head + i for i, bit in enumerate(path) if bit)
    pos = expected_head + 49
    for value in physical:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    state, head, ones = START, 0, set()
    for step in range(1, 100001):
        w, d, state = rows[state, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        assert state != HALT, ('blank halt during startup', step)
        if (state, head, ones) == (84, expected_head, expected):
            return {'steps': step, 'state': state, 'head': head,
                    'physical_file': physical, 'complete_tape_equality': True,
                    'one_cells': sorted(ones)}
    raise AssertionError('Exact clean frame not reached')


def build(output=None, full=True):
    if not __debug__:
        raise SystemExit('Run without Python -O; assertions check the certificate.')
    c.machine, c.raw_nodes = ORIGINAL_MACHINE, ORIGINAL_NODES
    c.PHYSICAL[:] = ORIGINAL_PHYSICAL
    inc = ('leaf', 'inc', 1)
    c.MACROS[(inc, inc)] = 99
    c.MACROS[((inc, inc), (inc, inc))] = 190
    grammar = c.read_grammar(HERE / 'source/pa194.grammar.json')
    parent_grammar = c.read_grammar(HERE / 'inputs/parent195S.grammar.json')
    assert word(expanded(grammar)) == word(expanded(parent_grammar))
    assert len(word(expanded(grammar))) == 190
    sites, instructions, contracts = c.source(grammar)
    parent_sites, parent_instructions, parent_contracts = c.source(parent_grammar)
    assert instructions == parent_instructions
    assert [(op, arg) for path, op, arg in sites] == [
        (op, arg) for path, op, arg in parent_sites]
    assert len(sites) == 3673 and len(contracts) == 4780
    assert json.loads(json.dumps(instructions)) == json.loads(
        (HERE / 'source/pa194.instructions.json').read_text())
    assert [[''.join(map(str, p)), op, arg] for p, op, arg in sites] == json.loads(
        (HERE / 'source/pa194.sites.json').read_text())

    raw, index, shape = c.build(grammar)
    parent_raw, parent_index, parent_shape = c.build(parent_grammar)
    assert len(shape) == len(parent_shape) == 67 and len(raw) == 402
    fixed = {key: value for key, value in raw.items() if key[0] < 1300}
    assert len(fixed) == 268
    assert fixed == {key: value for key, value in parent_raw.items() if key[0] < 1300}
    folds = json.loads((HERE / 'source/pa194.folds.json').read_text())
    parent_folds = json.loads((HERE / 'inputs/parent195S.folds.json').read_text())
    assert len(folds) == 7 and len(parent_folds) == 6
    child, aliases = apply_folds(raw, folds)
    parent, parent_aliases = apply_folds(parent_raw, parent_folds)
    local = check_local_folds(raw, child, aliases, folds)
    check_local_folds(parent_raw, parent, parent_aliases, parent_folds)
    assert len(local['cases']) == 28
    assert parent == read_table(HERE / 'inputs/parent195S.native.tm')
    assert raw == read_table(HERE / 'tables/unfolded201.native.tm')
    assert child == read_table(HERE / 'tables/pa194.native.tm')
    original, _ = ORIGINAL_MACHINE()
    assert all(child[q, bit] == original[q, bit]
               for q in c.BOXSTATES for bit in (0, 1))
    valid = c.validate(child, contracts) if full else None
    parent_valid = c.validate(parent, parent_contracts) if full else None
    if full:
        assert valid['ok'] and parent_valid['ok']
    blank = startup(child, sites[25][0])
    parent_blank = startup(parent, parent_sites[25][0])
    assert blank['steps'] == parent_blank['steps'] == 58154
    dense, labels = dense_table(child)
    native_text, dense_text = table_text(child), table_text(dense)
    assert (HERE / 'tables/pa194.tm').read_text() == dense_text
    assert json.loads((HERE / 'tables/pa194.labels.json').read_text()) == labels
    hashes = {'native': hashlib.sha256(native_text.encode()).hexdigest(),
              'dense': hashlib.sha256(dense_text.encode()).hexdigest()}
    assert hashes == {'native': EXPECTED_NATIVE, 'dense': EXPECTED_DENSE}
    receipt = {'working_states': 194, 'transitions': 388, 'fixed_states': 134,
               'raw_reader_states': 67, 'simultaneous_folds': 7,
               'graph_reachable_working_states': len(labels) - 1,
               'native_start': 74, 'native_halt': 254, 'dense_start': 0, 'dense_halt': 194,
               'macro_tokens': 190, 'macro_word_equal_to_parent195S': True,
               'source_sites': len(sites), 'complete_resolved_source_graph_equal': True,
               'arithmetic_box_rows_unchanged': True,
               'local_cases': len(local['cases']),
               'maximum_local_duration': max(x['duration'] for x in local['cases']),
               'incoming_fold_rows': len(local['incoming_rows']),
               'full_symbolic_validation_performed': full, 'symbolic_runtime': valid,
               'parent_symbolic_runtime': parent_valid, 'startup': blank,
               'parent_startup': parent_blank, 'sha256': hashes,
               'proof_scope': 'Finite and symbolic executable certificates with unchanged imported arithmetic-block lemmas; no new Lean endpoint'}
    if output is not None:
        output = Path(output)
        output.mkdir(parents=True, exist_ok=True)
        (output / 'pa194.native.tm').write_text(native_text)
        (output / 'pa194.tm').write_text(dense_text)
        (output / 'pa194.labels.json').write_text(json.dumps(labels) + '\n')
        (output / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if full:
        (HERE / 'evidence/pa194.verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
        (HERE / 'evidence/pa194.local-cases.json').write_text(json.dumps(local, indent=2) + '\n')
    return child, sites, instructions, receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Also write reconstructed tables to this directory')
    args = parser.parse_args()
    _, _, _, receipt = build(args.output)
    print(json.dumps(receipt, indent=2))
