#!/usr/bin/env python3
"""Reproduce the canonical-membership-binder 225-state parent of K224.

No optimization or sampled execution occurs in this builder. Input files are
pinned by SHA-256. It verifies the exact source changes, finite all-register
macro bisimulations, both complete guarded-CFG resolvers for each reassociation,
all decoder-prefix entries, and the complete blank startup.

The logical changes require the accompanying mathematical calibration note:
  * eight negation constructors (four double-negation pairs) in the K bundle are cancelled;
  * equality vacuity uses private binder 4*P(a,b)+1 instead of arbitrary c.
The eight logical rows, relational vacuity, gate, proof enumerator and register
encoding are retained. This file does not claim a new proof-assistant endpoint.
"""
from pathlib import Path
from functools import cache
from collections import defaultdict, Counter
import argparse
import hashlib
import json
import re
import sys

from local_bisimulation import check as local_bisimulation

PINS = {
    'results/candidate225.klabels.tm': '0847184fa05327daefa45c7012ce2c75fe58bf03d1dc930fe152e9fac55b4fbc',
    'results/sites225.json': '86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b',
    'baseline226/source/legacy_state_map.json': '8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151',
    'baseline226/vendor/k230-rocq/coq/prog/Dag230.v': '7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf',
}
EXPECTED_K_TABLE = '4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790'
EXPECTED_OLD_TABLE = 'b5111f270791fd0686df6f99af25648d7cf6e00ad57091b25b58e068abcd1898'
EXPECTED_SITES = '309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, move, target = line.split()
        table[int(q), int(bit)] = int(write), 1 if move == 'R' else -1, int(target)
    return table


def encode_table(table, start=0):
    return ('#! start %d\n' % start + ''.join(
        f'{q} {bit} {write} {"R" if move == 1 else "L"} {target}\n'
        for (q, bit), (write, move, target) in sorted(table.items()))).encode()


def replace_all(c, root, source, target):
    memo = {source: target}
    def visit(node):
        if node in memo:
            return memo[node]
        if c.leaf(node):
            return node
        result = visit(node[0]), visit(node[1])
        memo[node] = result
        return result
    return visit(root)


def decoder_map(c, table, root):
    states = defaultdict(set)
    paths = defaultdict(list)
    def visit(node, prefix, q):
        if c.leaf(node):
            return
        states[q].add(node)
        paths[q].append(prefix)
        for bit in (0, 1):
            if c.leaf(node[bit]):
                continue
            tape = {i: int(value) for i, value in enumerate(prefix + str(bit))}
            tape[-1] = 1
            before = tape.copy()
            head, state = len(prefix), q
            for _ in range(100):
                if head == len(prefix) + 1:
                    break
                if head not in tape:
                    raise ValueError(('Decoder left the known prefix', q, prefix, bit))
                write, move, state = table[state, tape[head]]
                tape[head] = write
                head += move
            if tape != before or head != len(prefix) + 1:
                raise ValueError(('Decoder prefix mismatch', q, prefix, bit))
            visit(node[bit], prefix + str(bit), state)
    visit(root, '', 84)
    return states, paths


def sole(states, q):
    if len(states[q]) != 1:
        raise ValueError(('Expected an unambiguous source entry', q))
    return next(iter(states[q]))


def set_row(table, q, bit, old, new, receipt):
    if table[q, bit] != old:
        raise ValueError(('Unexpected old transition', q, bit, table[q, bit], old))
    table[q, bit] = new
    receipt.append({'state': q, 'read': bit, 'old': list(old), 'new': list(new)})


def same_cfg(c, first, second):
    a, ca = c.graph_arithmetic(c.sites(first))
    b, cb = c.graph_arithmetic(c.sites(second))
    if a != b or a != c.graph_intervals(c.sites(first)) or b != c.graph_intervals(c.sites(second)):
        raise ValueError('A claimed closed reassociation changes the guarded source graph')
    return {'status': 'TWO_INDEPENDENT_GUARDED_CFG_RESOLVERS_AGREE',
            'source_instructions': len(a), 'first_no_stray_checks': ca,
            'second_no_stray_checks': cb}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-root', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'portable')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    baseline = args.baseline_root.resolve()
    for name, expected in PINS.items():
        if sha((baseline / name).read_bytes()) != expected:
            raise ValueError('Pinned input differs: ' + name)
    sys.path.insert(0, str(baseline / 'baseline226/verification'))
    import reconstruct227 as c
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    root0 = c.tree(json.loads((baseline / 'results/sites225.json').read_text()))
    table0 = read_table(baseline / 'results/candidate225.klabels.tm')
    q0, paths0 = decoder_map(c, table0, root0)
    N, I, Q = sole(q0, 184), sole(q0, 90), sole(q0, 86)
    A, X = sole(q0, 172), sole(q0, 180)
    AX = sole(q0, 167)
    one = N[0]
    assert N == (one, I)
    assert A == (N, (I, N))
    assert X == (N, (Q, N))
    assert AX == (A, X)
    old_final = sole(q0, 116)
    assert old_final[0] == old_final[1][0] == A
    gate_copy = old_final[1][1]
    assert c.boundary(gate_copy) == (0, 0, False)
    count = Counter()
    def census(node):
        count[node] += 1
        if not c.leaf(node):
            census(node[0]); census(node[1])
    census(root0)
    assert count[AX] == 3 and count[old_final] == 1

    # 1. Three existential/conjunction double-negation pairs and one bundle pair.
    fused_ax = N, ((I, Q), N)
    fused_final = N, ((I, I), (N, gate_copy))
    root1 = replace_all(c, replace_all(c, root0, AX, fused_ax), old_final, fused_final)
    table1 = table0.copy()
    stage1_rows = []
    edits1 = [
        (116, 0, (0, 1, 172), (0, 1, 184)),
        (116, 1, (1, 1, 192), (1, 1, 185)),
        (153, 1, (1, -1, 172), (1, -1, 167)),
        (167, 0, (0, 1, 172), (0, 1, 184)),
        (167, 1, (1, 1, 180), (1, 1, 192)),
        (172, 1, (1, 1, 185), (1, 1, 194)),
        (185, 0, (0, 1, 90), (0, 1, 150)),
        (185, 1, (1, 1, 184), (1, 1, 172)),
        (192, 0, (0, 1, 172), (0, 1, 157)),
        (192, 1, (1, 1, 194), (1, 1, 184)),
    ]
    for edit in edits1:
        set_row(table1, *edit, stage1_rows)
    decoder_map(c, table1, root1)

    # 2. Ex = (Neg,(All,Neg)) = (Push1,((Imp,All),Neg)).
    # The All/Neg alias disappears; state153 now has only the All/Imp role.
    new_x = one, ((I, Q), N)
    root2 = replace_all(c, root1, X, new_x)
    assert count[X] == 5  # Three were part of the cancelled And/Ex occurrences.
    cfg_ex = same_cfg(c, root1, root2)
    table2 = table1.copy()
    stage2_rows = []
    for edit in [(180, 0, (0, 1, 184), (0, 1, 152)),
                 (180, 1, (1, 1, 153), (1, 1, 192)),
                 (153, 1, (1, -1, 167), (1, 1, 90))]:
        set_row(table2, *edit, stage2_rows)
    q2, paths2 = decoder_map(c, table2, root2)

    # 3. Replace just the binder-producing word in equality vacuity.
    # Pc pushes c; R pushes wel(a,b) using the existing whole relation atom word.
    Pc, R, E = sole(q2, 166), sole(q2, 155), sole(q2, 182)
    AI, F, tail = sole(q2, 153), sole(q2, 116), sole(q2, 193)
    block, prefix = sole(q2, 224), sole(q2, 159)
    assert AI == (Q, I)
    assert prefix == (Pc, (R, (AI, E)))
    assert block == (prefix, (((Pc, E), (AI, F)), tail))
    for part in (Pc, R, E, AI, F, tail, prefix):
        assert c.boundary(part) == (0, 0, False)
    helper_block = prefix, (((R, E), (AI, F)), tail)
    root3 = replace_all(c, root2, block, helper_block)
    assert len(c.sites(root3)) - len(c.sites(root2)) == 54

    # 4. Three closed sequence rotations. They change no source instruction.
    final_block = (prefix, (R, E)), (AI, (F, tail))
    root4 = replace_all(c, root3, helper_block, final_block)
    cfg_suffix = same_cfg(c, root3, root4)
    table4 = table2.copy()
    stage4_rows = []
    for q, left, right in [(224, 135, 225), (135, 159, 191),
                            (225, 153, 100), (100, 116, 193), (191, 155, 182)]:
        for bit, target in enumerate((left, right)):
            old = table4[q, bit]
            new = bit, 1, target
            if old != new:
                set_row(table4, q, bit, old, new, stage4_rows)
    decoder_map(c, table4, root4)
    assert len(table4) == 450 and len({q for q, bit in table4}) == 225

    # Reconnect optimized arithmetic blocks to the exact upstream Dag230 macros.
    raw = (baseline / 'baseline226/vendor/k230-rocq/coq/prog/Dag230.v').read_text()
    dag = {int(q): (a, b) for q, a, b in re.findall(
        r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)', raw)}
    @cache
    def expand(q):
        def edge(text):
            if text == 'EHalt':
                return 'CH', None
            name, value = text.split(); value = int(value)
            if name == 'ENode':
                return expand(value)
            return {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB',
                    'EContinue': 'CC'}[name], value
        return tuple(edge(text) for text in dag[q])
    macro_inputs = {
        'Imp': (expand(119), I), 'All': (expand(180), Q),
        'Neg': (expand(218), N), 'And': (expand(178), A),
        'Exists': (expand(183), X), 'AndExists': (expand(110), AX),
        'PushOne': (expand(177), one), 'PushC': (expand(168), Pc),
        'RelationAtomAB': (((expand(166), expand(121)), expand(181)), R),
        'EqualityAtomAB': (((expand(166), expand(121)), expand(182)), E),
        'AllThenImp': ((expand(180), expand(119)), AI),
    }
    macro_proofs = {name: local_bisimulation(old, new)
                    for name, (old, new) in macro_inputs.items()}

    relabel = json.loads((baseline / 'baseline226/source/legacy_state_map.json').read_text())
    labels = {int(q): v for q, v in relabel['k230_to_old'].items()}
    labels[254] = 254
    def inherited(table):
        return {(labels[q], bit): (write, move, labels[target])
                for (q, bit), (write, move, target) in table.items()}
    boot0 = c.boot(inherited(table0), 409835)
    boot4 = c.boot(inherited(table4), 409835)
    assert boot0['state'] == boot4['state'] == 96
    assert boot0['head'] == boot4['head'] == -5
    assert boot0['one_cells'] == boot4['one_cells']
    assert boot0['all_other_cells'] == boot4['all_other_cells'] == 0

    working_raw = encode_table(table4)
    inherited_raw = c.encode(inherited(table4))
    source_raw = c.compact(c.sites(root4))
    assert sha(working_raw) == EXPECTED_K_TABLE
    assert sha(inherited_raw) == EXPECTED_OLD_TABLE
    assert sha(source_raw) == EXPECTED_SITES
    (output / 'candidate225.k.tm').write_bytes(working_raw)
    (output / 'candidate225.tm').write_bytes(inherited_raw)
    (output / 'sites225.json').write_bytes(source_raw)
    (output / 'helper_before_reassociation.json').write_bytes(c.compact(c.sites(root3)))
    (output / 'macro_certificates.json').write_text(json.dumps(macro_proofs, indent=2) + '\n')
    (output / 'bootstrap225.json').write_text(json.dumps(boot4, indent=2) + '\n')
    receipt = {
        'status': 'CANONICAL_REL225_EXACT_CONSTRUCTION_PASS', 'input_sha256': PINS,
        'logical_changes': ['Cancel eight negation constructors (four double-negation pairs) in the K bundle',
                            'Use membership-code binder kappa(a,b)=4*P(a,b)+1 in equality vacuity'],
        'retained': ['Eight logical rows', 'Full relational-vacuity family',
                     'Original c=a or c=b gate', 'Proof enumerator and nine-register encoding'],
        'stages': [
            {'name': 'baseline225', 'metrics': c.metrics(root0)},
            {'name': 'double_negation_fusion', 'metrics': c.metrics(root1), 'row_edits': stage1_rows},
            {'name': 'existential_reassociation', 'metrics': c.metrics(root2),
             'row_edits': stage2_rows, 'source_equivalence': cfg_ex},
            {'name': 'canonical_equality_binder', 'metrics': c.metrics(root3)},
            {'name': 'suffix_reassociation', 'metrics': c.metrics(root4),
             'row_edits': stage4_rows, 'source_equivalence': cfg_suffix}],
        'macro_checks': {name: {'status': v['status'], 'test_pairs': v['test_pairs']}
                         for name, v in macro_proofs.items()},
        'blank_startup': {'steps': 409835, 'head': -5, 'one_cells': 351,
                          'all_other_cells': 0, 'same_endpoint_as_original225': True},
        'working_states': 225, 'total_rows': 450,
        'output_sha256': {'candidate225.k.tm': sha(working_raw),
                          'candidate225.tm': sha(inherited_raw), 'sites225.json': sha(source_raw)},
        'scope': 'Exact finite construction, all-register local arithmetic bisimulations, '
                 'two complete guarded-CFG checks, decoder-prefix checks, and complete blank startup. '
                 'The accompanying universal-runtime certificate and logical calibration argument '
                 'are separate required parts of the non-halting/consistency equivalence.'}
    (output / 'construction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'states': 225, 'rows': 450,
                      'macro_checks': len(macro_proofs), 'source': c.metrics(root4),
                      'bootstrap_steps': 409835, 'sha256': receipt['output_sha256']}, indent=2))


if __name__ == '__main__':
    main()
