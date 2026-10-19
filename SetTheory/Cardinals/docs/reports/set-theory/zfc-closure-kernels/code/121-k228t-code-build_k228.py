#!/usr/bin/env python3
"""Deterministically reconstruct K228 from the exact released K230 inputs.

Python 3.10+ standard library only. This builder checks literal inputs, the
four exact closed source macros, their decoder entries, every row edit, all
state counts, complete source structure, and the canonical state bijection.
It does not replace the separate startup or unbounded runtime proofs.

Examples:
  python3 -B build_k228.py --k230-dir PATH_TO_K230_REPO --output-dir NEW_DIRECTORY
  python3 -B build_k228.py --machine k230.tm --sites sites230.json \
      --output-dir NEW_DIRECTORY

All outputs are deterministic bytes. Supplied inputs are never changed.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse
import hashlib
import json

INPUT_MACHINE_SHA256 = 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
INPUT_SITES_SHA256 = '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
NORMALIZED_SOURCE230_SHA256 = '0879180d27ae48f6d77001f8f32108c7f7b3f86df3deab86bc2bbb7e7266d588'
FINAL_ORIGINAL_SHA256 = '2b791ed22523b9610d43d7440631b27063089d2d1a24cf3bfbe5ace6cf416ea2'
FINAL_CANONICAL_SHA256 = '06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001'
FINAL_SOURCE_SHA256 = '61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b'
LOOP229_SHA256 = 'a4d7614b7bfc61f0c9934013f7bec6897aacc53978bc100613037b150f7a5645'
ROTATED230_SHA256 = 'ee3279c9a1cb499a30d21cef46d485976677640a43fa4e490d91affc6a010db2'
START, DISPATCHER, HALT = 0, 84, 230
OLD_MACRO = ((('CD', 6), (('CI', 5), ('CC', 2))), ('CI', 5))
NEW_MACRO = (('CI', 5), (('CD', 6), ('CC', 2)))
EXPECTED_OCCURRENCES = [
    '111010010010111111000011',
    '11101001001011111110011',
    '1110100101100011',
    '111110011',
]
EXPECTED_FINAL_EDITS = {
    (63, 0): (0, -1, 123),
    (63, 1): (1, -1, 30),
    (70, 1): (1, 1, 63),
    (71, 0): (0, -1, 91),
    (80, 1): (1, -1, 138),
    (121, 0): (0, 1, 63),
    (121, 1): (1, 1, 13),
    (126, 0): (0, 1, 71),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(value, compact=False):
    options = {'separators': (',', ':')} if compact else {'indent': 2}
    return (json.dumps(value, **options) + '\n').encode('utf-8')


def parse_machine(raw):
    table, starts = {}, []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            parts = line.split()
            require(len(parts) == 5, 'A machine row does not have five fields')
            q, bit, write, direction, target = parts
            q, bit, write, target = map(int, (q, bit, write, target))
            key = q, bit
            require(key not in table, 'Repeated machine row')
            require(bit in (0, 1) and write in (0, 1) and direction in ('L', 'R'),
                    'Invalid binary symbol or movement')
            table[key] = write, 1 if direction == 'R' else -1, target
    require(starts == [START], 'Input must declare exactly initial state 0')
    validate_machine(table, set(range(230)), HALT)
    return table


def validate_machine(table, working, halt):
    require(set(table) == {(q, bit) for q in working for bit in (0, 1)},
            'Incomplete table or incorrect working-state set')
    require({target for write, direction, target in table.values()} - working == {halt},
            'Unexpected halt target or dangling state reference')
    require(START in working and halt not in working, 'Invalid initial/halt state')


def machine_bytes(table, start=START):
    lines = [f'#! start {start}\n']
    for (q, bit), (write, direction, target) in sorted(table.items()):
        lines.append(f'{q} {bit} {write} {"R" if direction == 1 else "L"} {target}\n')
    return ''.join(lines).encode('ascii')


def parse_source(raw):
    supplied = json.loads(raw)
    require(isinstance(supplied, list), 'Source must be a list')
    opcode = {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB',
              'EContinue': 'CC', 'EHalt': 'CH'}
    result = []
    for item in supplied:
        require(isinstance(item, list) and len(item) == 2, 'Malformed source row')
        path, instruction = item
        require(isinstance(path, str) and path and set(path) <= {'0', '1'},
                'Invalid source address')
        require(isinstance(instruction, str), 'Malformed source instruction')
        words = instruction.split()
        require(words and words[0] in opcode, 'Unknown source instruction')
        op = opcode[words[0]]
        require(len(words) == (1 if op == 'CH' else 2), 'Wrong source instruction arity')
        operand = None if op == 'CH' else int(words[1])
        require(op == 'CH' or (op in ('CI', 'CD') and 0 <= operand < 9)
                or (op in ('CB', 'CC') and operand >= 1), 'Invalid source operand')
        result.append([path, op, operand])
    require(result == sorted(result), 'Released source rows must be in address order')
    return result


def is_leaf(node):
    return isinstance(node[0], str)


def source_tree(rows):
    trie = {}
    for path, op, operand in rows:
        node = trie
        for digit in path:
            require('leaf' not in node, 'A source leaf is a prefix of another address')
            node = node.setdefault(digit, {})
        require(not node, 'Repeated source address or non-prefix-free source')
        node['leaf'] = op, operand

    def close(node):
        if 'leaf' in node:
            require(set(node) == {'leaf'}, 'Source leaf has children')
            return node['leaf']
        require(set(node) == {'0', '1'}, 'Source tree is not full')
        return close(node['0']), close(node['1'])

    return close(trie)


def source_rows(root, path=''):
    if is_leaf(root):
        return [[path, root[0], root[1]]]
    return source_rows(root[0], path + '0') + source_rows(root[1], path + '1')


@lru_cache(None)
def boundary(node):
    if is_leaf(node):
        op, operand = node
        if op == 'CD':
            return 1, 0, False
        if op == 'CB':
            return operand, 0, False
        if op == 'CC':
            return 0, operand, False
        return 0, 0, op == 'CH'
    left, right = boundary(node[0]), boundary(node[1])
    return (max(max(left[0] - 1, 0), right[0]),
            max(left[1], max(right[1] - 1, 0)), left[2] or right[2])


def source_metrics(root):
    dag = set()

    def visit(node):
        if node in dag:
            return
        dag.add(node)
        if not is_leaf(node):
            visit(node[0])
            visit(node[1])

    visit(root)
    rows = source_rows(root)
    leaves = {path for path, op, operand in rows}
    prefixes = {path[:i] for path in leaves for i in range(len(path))}
    require(not leaves & prefixes, 'Generated source is not prefix-free')
    require(len(prefixes) == len(leaves) - 1, 'Generated source is not full')
    require(all(path + digit in prefixes or path + digit in leaves
                for path in prefixes for digit in ('0', '1')),
            'Generated source has a missing branch')
    counts = Counter(op for path, op, operand in rows)
    return dict(leaf_occurrences=len(rows), internal_occurrences=len(prefixes),
                dag_nodes=len(dag), maximum_depth=max(map(len, leaves)),
                maximum_zero_run=max(len(run) for path in leaves for run in path.split('1')),
                guarded_cases=len(rows) + counts['CD'], instruction_counts=dict(sorted(counts.items())),
                complete_prefix_free_binary_tree=True)


def rotate_source(root):
    occurrences = []

    def replace(node, path):
        if node == OLD_MACRO:
            occurrences.append(path)
            return NEW_MACRO
        if is_leaf(node):
            return node
        return replace(node[0], path + '0'), replace(node[1], path + '1')

    result = replace(root, '')
    require(occurrences == EXPECTED_OCCURRENCES, 'Unexpected transfer macro occurrences')
    require(boundary(OLD_MACRO) == boundary(NEW_MACRO) == (0, 0, False),
            'A transfer macro has an escaping control action')
    return result, occurrences


def check_macro_decoder_entries(table, occurrences):
    evidence = []
    for path in occurrences:
        state = DISPATCHER
        rows = []
        for digit in path:
            bit = int(digit)
            write, direction, target = table[state, bit]
            require((write, direction) == (bit, 1), 'Macro prefix is not a pure decoder path')
            rows.append([state, bit])
            state = target
        require(state == 121, 'Source transfer macro does not enter exact decoder state 121')
        evidence.append(dict(path=path, endpoint=state, literal_decoder_rows=rows))
    return evidence


def build(machine_raw, source_raw):
    require(sha(machine_raw) == INPUT_MACHINE_SHA256, 'Wrong released K230 machine bytes')
    require(sha(source_raw) == INPUT_SITES_SHA256, 'Wrong released K230 sites230.json bytes')
    old = parse_machine(machine_raw)
    old_source = parse_source(source_raw)
    root = source_tree(old_source)
    require(source_rows(root) == old_source, 'Source parser does not round-trip')
    old_metrics = source_metrics(root)
    root_new, occurrences = rotate_source(root)
    new_source = source_rows(root_new)
    new_metrics = source_metrics(root_new)
    require(boundary(root) == boundary(root_new) == (0, 0, True),
            'Unexpected whole-program break/continue/halt boundary')
    require((old_metrics['leaf_occurrences'], old_metrics['dag_nodes'],
             old_metrics['maximum_depth'], old_metrics['maximum_zero_run'],
             old_metrics['guarded_cases']) == (5125, 212, 40, 6, 6660),
            'Unexpected original source census')
    require((new_metrics['leaf_occurrences'], new_metrics['dag_nodes'],
             new_metrics['maximum_depth'], new_metrics['maximum_zero_run'],
             new_metrics['guarded_cases']) == (5121, 212, 40, 6, 6656),
            'Unexpected rotated source census')
    entries = check_macro_decoder_entries(old, occurrences)

    # First implement the source rotation without changing the state census.
    require((old[121, 0], old[121, 1]) == ((0, 1, 31), (1, 1, 63)),
            'Unexpected original transfer decoder')
    rotated = dict(old)
    rotated[121, 0], rotated[121, 1] = (0, 1, 63), (1, 1, 13)
    validate_machine(rotated, set(range(230)), HALT)

    # Transfer the independently certified 72/90 sharing, in K labels63/79.
    require(sorted(row for row, triple in rotated.items() if triple[2] == 79) == [(70, 1)],
            'Unexpected caller of folded state79')
    loop229 = {(q, bit): (write, direction, 63 if target == 79 else target)
               for (q, bit), (write, direction, target) in rotated.items() if q != 79}
    loop229[63, 0], loop229[63, 1] = (0, -1, 123), (1, -1, 30)
    validate_machine(loop229, set(range(230)) - {79}, HALT)

    # Compose the coordinated169/80 reduction, in K labels140/71.
    require(sorted(row for row, triple in loop229.items() if triple[2] == 140) == [(126, 0)],
            'Unexpected caller of folded state140')
    final = {(q, bit): (write, direction, 71 if target == 140 else target)
             for (q, bit), (write, direction, target) in loop229.items() if q != 140}
    final[71, 0], final[80, 1] = (0, -1, 91), (1, -1, 138)
    working = set(range(230)) - {79, 140}
    validate_machine(final, working, HALT)
    actual_edits = {row: final[row] for row in final if final[row] != old[row]}
    require(actual_edits == EXPECTED_FINAL_EDITS, 'The final edit set is not exactly the specified eight rows')
    require(set(old) - set(final) == {(q, bit) for q in (79, 140) for bit in (0, 1)},
            'Unexpected deleted row')

    # A literal alpha-renaming supplies contiguous working states and halt228.
    order = sorted(working)
    old_to_new = {q: i for i, q in enumerate(order)}
    old_to_new[HALT] = 228
    canonical = {(old_to_new[q], bit): (write, direction, old_to_new[target])
                 for (q, bit), (write, direction, target) in final.items()}
    validate_machine(canonical, set(range(228)), 228)
    require(old_to_new[START] == 0 and old_to_new[DISPATCHER] == 83,
            'Unexpected canonical start/dispatcher labels')
    require(len(set(old_to_new.values())) == len(old_to_new) == 229,
            'Canonical state map is not a bijection')
    reverse = {i: q for q, i in old_to_new.items()}
    recovered = {(reverse[q], bit): (write, direction, reverse[target])
                 for (q, bit), (write, direction, target) in canonical.items()}
    require(recovered == final, 'Inverse canonical renaming does not reproduce the literal table')

    normalized_original = json_bytes(old_source, compact=True)
    normalized = json_bytes(new_source, compact=True)
    raw_rotated, raw_loop, raw_final, raw_canonical = map(machine_bytes,
                                                       (rotated, loop229, final, canonical))
    require(sha(raw_rotated) == ROTATED230_SHA256, 'Rotated230 byte mismatch')
    require(sha(raw_loop) == LOOP229_SHA256, 'Loop229 byte mismatch')
    require(sha(raw_final) == FINAL_ORIGINAL_SHA256, 'Final original-label228 byte mismatch')
    require(sha(raw_canonical) == FINAL_CANONICAL_SHA256, 'Final canonical228 byte mismatch')
    require(sha(normalized_original) == NORMALIZED_SOURCE230_SHA256,
            'Original normalized source byte mismatch')
    require(sha(normalized) == FINAL_SOURCE_SHA256, 'Final normalized source byte mismatch')
    mapping = dict(old_to_new=old_to_new, new_to_old=order + [HALT],
                   deleted_original_states=[79, 140], start_old=0, start_new=0,
                   dispatcher_old=84, dispatcher_new=83, halt_old=230, halt_new=228)
    outputs = {
        'k230_rotated.tm': raw_rotated,
        'k229_loop.tm': raw_loop,
        'k228_original_labels.tm': raw_final,
        'k228.tm': raw_canonical,
        'sites230_logical.json': normalized_original,
        'sites_transfer5121.json': normalized,
        'renumbering228.json': json_bytes(mapping),
    }
    edits = [dict(row=list(row), before=list(old[row]), after=list(final[row]))
             for row in sorted(actual_edits)]
    receipt = dict(
        status='PASS_DETERMINISTIC_CONSTRUCTION_AND_STRUCTURAL_CHECKS',
        input_machine_sha256=INPUT_MACHINE_SHA256,
        input_sites_sha256=INPUT_SITES_SHA256,
        working_states=228, transition_rows=456, alphabet=[0, 1],
        tape='One two-sided infinite tape; all-zero blank input', moves=['L', 'R'],
        initial_state=0, canonical_dispatcher=83, canonical_halt=228,
        original_dispatcher=84, original_halt=230,
        intermediate_working_states={'rotated': 230, 'loop_fold': 229, 'final': 228},
        deleted_original_states=[79, 140], changed_surviving_row_count=8,
        changed_surviving_rows=edits,
        deleted_rows=[dict(row=list(row), transition=list(old[row]))
                      for row in sorted(set(old) - set(final))],
        source_rewrite='((CD6,(CI5,CC2)),CI5) -> (CI5,(CD6,CC2))',
        source_old_macro=OLD_MACRO, source_new_macro=NEW_MACRO,
        source_old_boundary=boundary(OLD_MACRO), source_new_boundary=boundary(NEW_MACRO),
        whole_old_source_boundary=boundary(root), whole_new_source_boundary=boundary(root_new),
        source_occurrence_count=len(occurrences), source_occurrences=occurrences,
        source_decoder_entries=entries, old_source_metrics=old_metrics,
        final_source_metrics=new_metrics,
        source_equivalence_kind='Four closed transfer-plus-one macro replacements; not leaf-graph identity',
        source_macro_theorem='For all natural a,b, both fragments terminate normally, map '
            '(R5,R6)=(a,b) to (a+b+1,0), and preserve all other registers. '
            'The separate mathematical proof is induction on b and contextual replacement.',
        logical_to_physical=[6, 2, 0, 4, 3, 7, 8, 5, 1],
        canonical_bijection_verified=True,
        output_sha256={name: sha(raw) for name, raw in outputs.items()},
        scope='Exact construction, source structure, literal decoder entries, edits and '
            'renumbering only. Startup, local fold and unbounded instruction proofs '
            'are separate verification steps; this builder does not assert their execution.')
    outputs['construction228.json'] = json_bytes(receipt)
    return outputs, receipt


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k230-dir', type=Path, help='Released K230 repository root')
    ap.add_argument('--machine', type=Path, help='Exact released machine/k230.tm')
    ap.add_argument('--sites', type=Path, help='Exact released machine/sites230.json')
    ap.add_argument('--output-dir', type=Path, help='New or empty output directory')
    ap.add_argument('--check', action='store_true', help='Rebuild in memory and compare every packaged artifact')
    args = ap.parse_args()
    if args.k230_dir is not None:
        require(args.machine is None and args.sites is None,
                'Choose --k230-dir or explicit --machine/--sites, not both')
        args.machine = args.k230_dir / 'machine/k230.tm'
        args.sites = args.k230_dir / 'machine/sites230.json'
    package = Path(__file__).resolve().parent.parent
    if args.machine is None and args.sites is None:
        args.machine, args.sites = package/'inputs/k230.tm', package/'inputs/sites230.json'
    require(args.machine is not None and args.sites is not None,
            'Supply both --machine and --sites')
    require(args.check != (args.output_dir is not None),
            'Choose exactly --check or --output-dir')
    if args.check:
        outputs, receipt = build(args.machine.read_bytes(), args.sites.read_bytes())
        destinations = {
            'k230_rotated.tm': 'machines/k230_rotated.tm',
            'k229_loop.tm': 'machines/k229_loop.tm',
            'k228_original_labels.tm': 'machines/k228_original_labels.tm',
            'k228.tm': 'machines/k228.tm',
            'sites230_logical.json': 'inputs/sites230_logical.json',
            'sites_transfer5121.json': 'machines/sites228.json',
            'renumbering228.json': 'machines/renumbering228.json',
            'construction228.json': 'evidence/construction228.json',
        }
        for name, raw in outputs.items():
            require((package/destinations[name]).read_bytes() == raw,
                    'Packaged artifact does not match reconstruction: '+name)
        print('PASS: all eight artifacts reproduced byte-for-byte; 228 states, 456 rows, canonical bijection exact')
        return
    require(not args.output_dir.exists() or
            (args.output_dir.is_dir() and not any(args.output_dir.iterdir())),
            'Choose a new or empty output directory')
    outputs, receipt = build(args.machine.read_bytes(), args.sites.read_bytes())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, raw in outputs.items():
        (args.output_dir / name).write_bytes(raw)
    print(json.dumps({key: receipt[key] for key in
          ('status', 'working_states', 'transition_rows', 'source_occurrence_count',
           'canonical_dispatcher', 'canonical_halt', 'output_sha256')}, indent=2))


if __name__ == '__main__':
    main()
