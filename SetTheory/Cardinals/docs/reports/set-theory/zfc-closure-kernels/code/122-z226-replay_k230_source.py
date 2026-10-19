#!/usr/bin/env python3
"""Replay the K230 source normalization and exact finite CFG certificates.

Requires only Python's standard library and the adjacent source_tools.py.
It deliberately makes no assertion about the binary machine: decoder helper
entries, state folds, blank initialization and symbolic runtime have separate
certificates.  The output is the exact source interpreted by that machine.
"""
from pathlib import Path
import argparse
import hashlib
import json
import source_tools as s

INPUT_SHA256 = '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
LOOP_SHA256 = '61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b'
FINAL_SHA256 = '31aaece78d025fbc262e742411e75e24eef9435fe196c67e65b995e8b833fe61'
OLD = ((('CD', 6), (('CI', 5), ('CC', 2))), ('CI', 5))
NEW = (('CI', 5), (('CD', 6), ('CC', 2)))
MACRO = ('TOTAL_TRANSFER_PLUS_ONE', 5, 6)
LOOP_PATHS = [
    '111010010010111111000011',
    '11101001001011111110011',
    '1110100101100011',
    '111110011',
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def serial(tree):
    return s.json_bytes(s.sites(tree), compact=True)


def occurrences(tree, target, path=''):
    if tree == target:
        return [path]
    if s.is_leaf(tree):
        return []
    return (occurrences(tree[0], target, path + '0') +
            occurrences(tree[1], target, path + '1'))


def substitute(tree, old, new):
    if tree == old:
        return new
    if s.is_leaf(tree):
        return tree
    return substitute(tree[0], old, new), substitute(tree[1], old, new)


def at_path(tree, path):
    for bit in path:
        require(not s.is_leaf(tree), 'Rotation path descends through a leaf')
        tree = tree[int(bit)]
    return tree


def load_original(raw):
    require(sha(raw) == INPUT_SHA256, 'Pinned source hash mismatch')
    names = {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB',
             'EContinue': 'CC', 'EHalt': 'CH'}
    rows = []
    for path, instruction in json.loads(raw):
        words = instruction.split()
        rows.append((path, names[words[0]],
                     int(words[1]) if len(words) == 2 else None))
    require(len(rows) == 5125, 'Original source census mismatch')
    return s.tree(rows)


def normalize_loops(root):
    require(occurrences(root, OLD) == LOOP_PATHS,
            'Transfer-loop occurrence census mismatch')
    require(s.boundary(OLD) == s.boundary(NEW) == (0, 0, False),
            'Transfer loops must be closed and contain no halt')
    result = substitute(root, OLD, NEW)
    require(substitute(root, OLD, MACRO) == substitute(result, NEW, MACRO),
            'Surrounding source contexts differ')
    require(sha(serial(result)) == LOOP_SHA256, 'Normalized source hash mismatch')
    # The certificate's infinite-register argument is the natural-number
    # induction on R6: both total macros execute 3*R6+2 steps, add R6+1
    # to R5, set R6 to zero and leave every other register unchanged.
    return result


def apply_stage(root, record, index):
    require(sha(serial(root)) == record['before_source_sha256'],
            f'Stage {index}: input hash mismatch')
    paths = record['occurrence_paths']
    require(paths, f'Stage {index}: missing occurrence paths')
    old = at_path(root, paths[0])
    require(occurrences(root, old) == paths,
            f'Stage {index}: shared-subtree occurrence mismatch')
    require(not s.is_leaf(old), f'Stage {index}: outer node is a leaf')
    if record['direction'] == 'left':
        a, inner = old
        require(not s.is_leaf(inner), f'Stage {index}: right child is a leaf')
        b, c = inner
        new = ((a, b), c)
    else:
        require(record['direction'] == 'right', f'Stage {index}: bad direction')
        inner, c = old
        require(not s.is_leaf(inner), f'Stage {index}: left child is a leaf')
        a, b = inner
        new = (a, (b, c))
    require([len(s.sites(x)) for x in (a, b, c)] == record['chunk_leaf_counts'],
            f'Stage {index}: chunk census mismatch')
    require([list(s.boundary(x)) for x in (a, b, c)] == record['chunk_boundaries'],
            f'Stage {index}: chunk boundary mismatch')
    result = substitute(root, old, new)
    require(sha(serial(result)) == record['after_source_sha256'],
            f'Stage {index}: output hash mismatch')
    before_rows, before_edges, before_entry = s.graph(s.sites(root))
    after_rows, after_edges, after_entry = s.graph(s.sites(result))
    require([x[1:] for x in before_rows] == [x[1:] for x in after_rows],
            f'Stage {index}: opcode/register sequence changed')
    require(before_edges == after_edges and before_entry == after_entry,
            f'Stage {index}: guarded successor graph changed')
    metrics = s.metrics(result)
    for key in ('maximum_zero_run', 'maximum_depth', 'dag_nodes'):
        require(metrics[key] == record[key], f'Stage {index}: metric mismatch: {key}')
    return result, dict(stage=index,
        outer_state=record['outer_state'], inner_state=record['inner_state'],
        direction=record['direction'], shared_occurrences=len(paths),
        opcode_and_operand_checks=len(before_rows),
        guarded_edge_checks=sum(len(x) - (2 if x[0] in ('INC', 'DEC') else 1)
                                for x in before_edges),
        changed_paths=sum(x[0] != y[0] for x, y in zip(before_rows, after_rows)),
        output_sha256=sha(serial(result)), metrics=metrics)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-source', type=Path, required=True,
                        help='Pinned k230-rocq machine/sites230.json')
    parser.add_argument('--rotations', type=Path, required=True,
                        help='The source_rotations.json certificate')
    parser.add_argument('--output', type=Path, required=True,
                        help='Directory for regenerated source and replay receipt')
    args = parser.parse_args()
    root = load_original(args.input_source.read_bytes())
    normalized = normalize_loops(root)
    root = normalized
    certificate_raw = args.rotations.read_bytes()
    certificate = json.loads(certificate_raw)
    require(certificate['initial_source_sha256'] == LOOP_SHA256,
            'Rotation certificate starts from wrong source')
    require(len(certificate['stages']) == 13, 'Expected exactly 13 rotations')
    stages = []
    for index, record in enumerate(certificate['stages'], 1):
        root, check = apply_stage(root, record, index)
        stages.append(check)
    final_raw = serial(root)
    require(sha(final_raw) == certificate['final_source_sha256'] == FINAL_SHA256,
            'Final source hash mismatch')
    original_rows, original_edges, entry = s.graph(s.sites(normalized))
    final_rows, final_edges, final_entry = s.graph(s.sites(root))
    require(original_edges == final_edges and entry == final_entry,
            'Final source graph mismatch')
    require([x[1:] for x in original_rows] == [x[1:] for x in final_rows],
            'Final source instruction mismatch')
    receipt = dict(status='EXACT_SOURCE_REPLAY_PASS',
        input_source_sha256=INPUT_SHA256, normalized_source_sha256=LOOP_SHA256,
        final_source_sha256=FINAL_SHA256,
        rotation_certificate_sha256=sha(certificate_raw),
        total_closed_macros_replaced=len(LOOP_PATHS),
        total_source_rotations=len(stages), stages=stages,
        final_metrics=s.metrics(root),
        final_runtime_guard_cases=sum(2 if op == 'CD' else 1 for _, op, _ in final_rows),
        paths_relocated=sum(a[0] != b[0] for a, b in zip(original_rows, final_rows)),
        proof_scope='Natural-number induction for four closed total macros; '
                    'exact finite guarded-CFG isomorphism for all rotations. '
                    'These imply unbounded source-halting equivalence. '
                    'Binary runtime, primitive callbacks and blank startup '
                    'are certified separately.')
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'sites_normalized.json').write_bytes(serial(normalized))
    (args.output / 'sites_logical.json').write_bytes(final_raw)
    (args.output / 'source_replay_receipt.json').write_bytes(s.json_bytes(receipt))
    print(json.dumps({k: receipt[k] for k in ('status', 'final_source_sha256',
          'total_source_rotations', 'final_metrics', 'final_runtime_guard_cases')}))


if __name__ == '__main__':
    main()
