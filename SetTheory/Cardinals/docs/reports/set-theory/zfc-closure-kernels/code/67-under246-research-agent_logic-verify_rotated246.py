#!/usr/bin/env python3
"""Independent certification and canonical naming of the rotated 246 control.

The exact table is preserved.  This checker independently parses it, validates
source reassociation with the guarded leaf graph, replays the previously
proved register induction engine while recording every supporting row,
checks all symbolic source instruction cases, and replays the complete blank
bootstrap on a dense tape for both old and canonical state names.

It deliberately reuses the pinned prefix-affine and macro-induction engines;
it is an ordinary mathematical certificate checker, not a proof-assistant
kernel endpoint or a new claim below 246 working states.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

from verify_reassociation import Decoder, read_json, read_literal, encode as json_encode

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
BASE = RESEARCH / 'sources/context246/zfc-context246'
CANDIDATE = RESEARCH / 'agent_state/rebracket/unshared246.tm'
SOURCE = RESEARCH / 'root_search/rebracket202_minimal.json'
ORIGINAL = RESEARCH / 'sources/beyond252/beyond252/exploratory/data/original203.json'
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SKIP = (60, 44, 31, 56, 38, 40, 28, 64, 69)
EXPECTED = {
    'candidate': 'e27b5d90abae92dae72a728d161d7e46b0dcbb19233afc8bc67e972efd5384ee',
    'baseline': '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee',
    'source': '41e5dac5ecec532dec144c6f4196e50b25c32c7b8a042656a6a3892c4c0ad76f',
    'macro': '3484c0be3aaf34bd3677c0cc727eaba8655efd358f9338192a88be0d9c89ad8d',
    'affine': '083f884e6de87a85381ebc6b28c23d02a9f0731e67c3d77e26ed9ea4544cd08e',
    'rebuild_dependency': 'b498967f2984eaea9d21f94efc39e57bc1c2c659cbf23efc89a4a010b8a39e0b',
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_tm(path):
    table = {}
    start = None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        assert q >= 0 and target >= 0
        assert b in (0, 1) and w in (0, 1) and direction in ('L', 'R')
        assert (q, b) not in table
        table[q, b] = (w, direction, target)
    states = {q for q, _ in table}
    assert start in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    outside = {target for _, _, target in table.values()} - states
    assert len(outside) == 1
    return table, start, outside.pop()


def encode_tm(table, start):
    return f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {d} {s}\n' for (q, b), (w, d, s) in sorted(table.items()))


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class Tracked(dict):
    def __init__(self, table):
        super().__init__(table)
        self.used = set()

    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def replay_inductions(macro, table):
    tracked = Tracked(table)
    macro.TABLE = tracked
    macro.DERIVED.clear()
    macro.BLOCK_PROOFS.clear()
    macro.WORD_IDENTITY_PROVED = False
    macro.prove_blocks()
    word = macro.prove_word_identity()
    operations = macro.prove_macros()
    marks = macro.prove_marks()
    result = {'blocks': list(macro.BLOCK_PROOFS.values()),
              'word_identity': word, 'operations': operations, 'marks': marks}
    return result, tracked.used


def check_oracle(affine):
    assert affine.SKIP == {str(q): r for r, q in enumerate(SKIP)}
    checked = 1
    for r, q in enumerate(SKIP):
        assert affine.oracle(str(q), None, ('plain', None)) == (
            '2' if r == 0 else '6', ('mark', r), 0)
        assert affine.oracle('73', None, ('mark', r)) == (
            '48', ('plain', ('inc', r)), 0)
        assert affine.oracle('95', None, ('mark', r)) is None
        checked += 3
        for zero in (True, False):
            expected = ('112', ('plain', None), 0) if zero else (
                '48', ('plain', ('dec', r)), 1)
            assert affine.oracle('95', (r, zero), ('mark', r)) == expected
            checked += 1
            for wrong in range(9):
                if wrong != r:
                    assert affine.oracle('95', (wrong, zero), ('mark', r)) is None
                    checked += 1
        for q in SKIP:
            for effect in ('inc', 'dec'):
                assert affine.oracle(str(q), None, ('plain', (effect, r))) is None
                checked += 1
    return checked


def check_instructions(affine, table, source):
    table = Tracked({(str(q), b): (w, d, str(s)) for (q, b), (w, d, s) in table.items()})
    counts, rules = Counter(), Counter()
    minimum = 10**9
    max_rules = 0
    overflow_count = 0
    def increment(word):
        return Decoder.increment(word), all(c == '1' for c in word)
    for word, e in source.sites:
        op = e[0]
        operand = PHYSICAL[e[1]] if op in ('I', 'D') else (e[1] if len(e) == 2 else None)
        assert len(word) <= 40
        for zero in ((True, False) if op == 'D' else (None,)):
            branch = (operand, zero) if op == 'D' else None
            extra, effect, overflow = 0, None, False
            if op == 'I':
                after, overflow = increment(word)
                effect = ('inc', operand)
            elif op == 'D' and not zero:
                after, overflow = increment(word)
                effect, extra = ('dec', operand), 1
            elif op == 'D':
                after, overflow = increment(Decoder.strip(word, '0', 1))
            elif op == 'B':
                after, overflow = increment(Decoder.strip(word, '0', operand))
            elif op == 'C':
                after = Decoder.strip(word, '1', operand)
            else:
                assert op == 'H'
                after = ''
            gap = 40 + extra + int(overflow) - len(after)
            assert gap >= 0
            target = affine.canon([('b', 1)],
                [('b', int(bit)) for bit in after] +
                [('r', 0, 1, gap), ('b', 1), ('box', ('plain', effect))])
            counts_this, steps = affine.run(table, word, branch, target,
                                           halt=op == 'H', fuel=1500)
            assert steps > 0
            counts[op + ('/zero' if zero else '/positive') if op == 'D' else op] += 1
            rules.update(counts_this)
            minimum = min(minimum, steps)
            max_rules = max(max_rules, sum(counts_this.values()))
            overflow_count += int(overflow)
    assert sum(counts.values()) == 8391
    return {
        'guarded_cases': sum(counts.values()), 'by_operation': dict(counts),
        'minimum_literal_steps': minimum, 'maximum_symbolic_rules': max_rules,
        'overflow_cases': overflow_count, 'symbolic_rule_counts': dict(rules),
        'literal_pairs_used': len(table.used),
        'scope': 'All nonnegative gap parameters and all complete register files satisfying the named source guard and nonempty spare premise.'
    }, {(int(q), b) for q, b in table.used}


def expected_boot_ones():
    values = [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167
    result = {-6, 176}
    at = 177
    for value in values:
        at += 1  # The block's initial zero.
        for _ in range(value + 1):
            result.add(at)
            at += 1
    assert at == 702 and len(result) == 351
    return result


def dense_boot(table, start, halt, wanted_root, steps=410735):
    # Every head position in the first steps moves lies in [-steps,steps].
    # This fixed dense array covers that entire interval with extra endpoints.
    origin = steps + 1
    tape = bytearray(2 * steps + 3)
    head = origin
    q = start
    lowest = highest = head
    used = Counter()
    for _ in range(steps):
        assert q != halt
        symbol = tape[head]
        used[q, symbol] += 1
        write, direction, q = table[q, symbol]
        tape[head] = write
        head += 1 if direction == 'R' else -1
        lowest, highest = min(lowest, head), max(highest, head)
    ones = {i - origin for i, b in enumerate(tape) if b}
    assert q == wanted_root and head - origin == -5
    assert ones == expected_boot_ones()
    ordered_ones = sorted(ones)
    return {
        'steps': steps, 'start_state': start, 'exit_state': q,
        'head': head - origin, 'marker': -6, 'header': 176, 'header_distance': 181,
        'pc': '', 'gap_parameter_at_minimum_40': 141,
        'physical_registers': [0, 0, 0, 3, 0, 0, 3, 0, 0],
        'logical_registers': [3, 0, 0, 0, 3, 0, 0, 0, 0],
        'spare_count': 167, 'all_spare_values': 1,
        'one_count': len(ones),
        'one_positions_sha256': hashlib.sha256(json_encode(ordered_ones)).hexdigest(),
        'all_other_cells_zero': True,
        'head_interval_visited': [lowest - origin, highest - origin],
        'distinct_transition_pairs_used': len(used),
        'verification': 'Entire dense tape equals the explicitly generated root frame, not merely a bounded observation window.'
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--candidate', type=Path, default=CANDIDATE)
    ap.add_argument('--base-package', type=Path, default=BASE)
    ap.add_argument('--source', type=Path, default=SOURCE)
    ap.add_argument('--original-source', type=Path, default=ORIGINAL)
    ap.add_argument('--output', type=Path, default=HERE / 'rotated246')
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions must be enabled')
    started = time.monotonic()
    baseline_path = args.base_package / 'machine/zfc_prefix246_old.tm'
    macro_path = args.base_package / 'code/check_macro_inductions.py'
    affine_path = args.base_package / 'sources/prior/prefix_affine.py'
    rebuild_path = args.base_package / 'code/rebuild_machines.py'
    paths = {'candidate': args.candidate, 'baseline': baseline_path,
             'source': args.source, 'macro': macro_path, 'affine': affine_path,
             'rebuild_dependency': rebuild_path}
    for key, path in paths.items():
        assert digest(path) == EXPECTED[key], ('pinned file hash', key)
    table, start, halt = read_tm(args.candidate)
    baseline, old_start, old_halt = read_tm(baseline_path)
    assert start == old_start == 95 and halt == old_halt == 254
    assert len(table) == 492 and set(table) == set(baseline)
    changes = [(q, b, baseline[q, b], row)
               for (q, b), row in sorted(table.items()) if row != baseline[q, b]]
    assert {(q, b): new for q, b, old, new in changes} == {
        (178, 0): (0, 'R', 16), (178, 1): (1, 'R', 206),
        (208, 0): (0, 'R', 23), (208, 1): (1, 'R', 70),
        (218, 0): (0, 'R', 105), (237, 0): (0, 'R', 208),
    }
    assert encode_tm(table, start).encode('ascii') == args.candidate.read_bytes()

    # Source verification is independent of the compiler and its cached sites.
    nodes, root, _ = read_json(args.source)
    old_nodes, old_root, _ = read_json(args.original_source)
    source, original = Decoder(nodes, root), Decoder(old_nodes, old_root)
    literal_nodes, literal_root = read_literal(args.base_package / 'sources/Prog254.v')
    literal = Decoder(literal_nodes, literal_root)
    assert original.tree(('N', old_root)) == literal.tree(('N', literal_root))
    assert source.graph() == original.graph()
    assert source.normal(('N', root)) == original.normal(('N', old_root))
    assert len(nodes) == len(source.reached) == 202 and root == 202

    sys.path.insert(0, str(args.base_package / 'code'))
    macro = load_module(macro_path, 'rotated246_macro_induction')
    old_proofs, old_support = replay_inductions(macro, baseline)
    new_proofs, new_support = replay_inductions(macro, table)
    assert old_support == new_support
    assert all(table[key] == baseline[key] for key in old_support)
    assert old_proofs == new_proofs
    assert len(old_support) == 42

    affine = load_module(affine_path, 'rotated246_prefix_affine')
    oracle_checks = check_oracle(affine)
    instructions, affine_support = check_instructions(affine, table, source)
    assert old_support | affine_support == set(table)

    order = [start] + sorted({q for q, b in table} - {start})
    names = {q: i for i, q in enumerate(order)} | {halt: 246}
    canonical = {(names[q], b): (w, d, names[s])
                 for (q, b), (w, d, s) in table.items()}
    assert set(canonical) == {(q, b) for q in range(246) for b in (0, 1)}
    canonical_text = encode_tm(canonical, 0)
    reached, todo = set(), [0]
    while todo:
        q = todo.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != 246:
            todo.extend(canonical[q, b][2] for b in (0, 1))
    assert reached == set(range(247))
    boot_old = dense_boot(table, start, halt, 96)
    boot_canonical = dense_boot(canonical, 0, 246, names[96])
    assert boot_old['one_positions_sha256'] == boot_canonical['one_positions_sha256']

    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    machine_path = output / 'zfc_rotated246.tm'
    machine_path.write_text(canonical_text, encoding='ascii')
    renaming = {'start_old': start, 'start_canonical': 0, 'halt_old': halt,
                'halt_canonical': 246, 'dispatch_old': 96, 'dispatch_canonical': names[96],
                'convention': 'Start first, then increasing old working-state labels; halt last.',
                'canonical_to_old': order, 'old_to_canonical': names}
    (output / 'renumbering.json').write_text(json.dumps(renaming, indent=2) + '\n')
    proof_support = [{'state': q, 'read': b, 'row': table[q, b]} for q, b in sorted(old_support)]
    (output / 'protected_macro_rows.json').write_text(json.dumps(proof_support, indent=2) + '\n')
    (output / 'bootstrap.json').write_text(json.dumps({'old_labels': boot_old, 'canonical_labels': boot_canonical}, indent=2) + '\n')
    result = {
        'status': 'PASS', 'working_states': 246, 'binary_transition_rows': 492,
        'canonical_start': 0, 'canonical_halt': 246,
        'canonical_table_sha256': digest(machine_path), 'pinned_hashes': EXPECTED,
        'changed_rows_from_pinned246': [
            {'state': q, 'read': b, 'old': old, 'new': new} for q, b, old, new in changes],
        'source': {'decoder_nodes': 202, 'root': root, 'leaf_count': len(source.sites),
                   'exact_original_guarded_leaf_cfg': True, 'ordered_normal_form_equal': True,
                   'metrics_root_prefix_max_zeros_max_depth': source.metrics()},
        'macros': {'protected_pairs_checked_identical': len(old_support),
                   'block_inductions': len(new_proofs['blocks']),
                   'register_operations': len(new_proofs['operations']),
                   'marking_selectors': len(new_proofs['marks']),
                   'complete_induction_replay_matches_pinned_baseline': True,
                   'oracle_signature_and_guard_checks': oracle_checks},
        'instructions': instructions,
        'all_492_rows_covered_by_literal_or_macro_proof': True,
        'all_working_states_and_halt_graph_reachable': True,
        'renumbering_is_exact_transition_isomorphism': True,
        'blank_bootstrap': boot_canonical,
        'old_label_dense_bootstrap_also_checked': True,
        'elapsed_seconds': time.monotonic() - started,
        'logical_scope': 'Existing safe-root source calibration transports through independently checked source equivalence and positive full-frame instruction simulations. This is an ordinary mathematical certificate, not a fresh end-to-end proof-assistant build.',
        'bound_scope': 'A valid alternate 246-state control; it does not meet a strict fewer-than-246 target.'
    }
    (output / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
