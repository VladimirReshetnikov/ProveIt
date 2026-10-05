#!/usr/bin/env python3
"""Original metadata-only242 source construction plus two handwritten ring cuts.
Frozen programs are never imported or run, and saved graphs are never evaluated.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

WORK = Path('/home/codex/.codex/worktrees/2a71/Proofs')
SHELF = WORK / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS = {
    'neary_woods_shared_size243_riemann.md': 'ace6c824a2ef1e0fddd32dcd30919a9e4b6fa2118d30705579322e1c2cc09586',
    'neary_woods_shared_size243_riemann.json': 'db9673ba90ca965273a961f6bfb7c03f0e0a512ec0850c2841be3091bdcc3620',
    'review_neary_woods_shared_size243_aristotle.md': 'c5a893ad9c09c7b2d35f25a68bf66fb611b0ed837799363dc338e9da7a7b6151',
}

def need(truth, message):
    if not truth:
        raise ValueError(message)


def fingerprint(raw):
    return sha256(raw).hexdigest()


def canonical_rows(rows):
    return fingerprint(json.dumps(rows, sort_keys=True, separators=(',', ':')).encode())


def wire_inputs(row):
    return [item for item in row[2:] if isinstance(item, str)]


def consumers(rows, node):
    return sorted(row[0] for row in rows if node in wire_inputs(row))


def audit_graph(rows, ports, last, recipes):
    known = set(ports)
    need(len(known) == len(ports), 'distinct supplied ports')
    produced = {}
    seen_shapes = {}
    duplicates = []
    roles = set()
    tally = Counter()
    for number, row in enumerate(rows):
        need(type(row) is list and len(row) == 4, 'four-field binary record')
        out, op, left, right = row
        need(type(out) is str and out not in known, 'unique output')
        need(op in ('+', '-', '*'), 'arithmetic gate kind')
        need(set(wire_inputs(row)) <= known, 'saved topological order')
        for item in (left, right):
            if type(item) is str or type(item) is int:
                continue
            need(type(item) is dict and set(item) == {'fixed_numeral'}, 'fixed numeral syntax')
            roles.add(item['fixed_numeral'])
        args = [json.dumps(item, sort_keys=True) for item in (left, right)]
        if op in ('+', '*'):
            args.sort()
        shape = (op, *args)
        if shape in seen_shapes:
            duplicates.append([seen_shapes[shape], out])
        seen_shapes[shape] = out
        produced[out] = row
        known.add(out)
        tally[op] += 1
    reach = set()
    frontier = [last]
    while frontier:
        node = frontier.pop()
        if node in reach:
            continue
        reach.add(node)
        if node in produced:
            frontier.extend(wire_inputs(produced[node]))
    need(set(produced) <= reach, 'all gates live')
    need(set(ports) <= reach, 'all supplied ports live')
    need(roles == set(recipes), 'all and only declared numeral roles live')
    return {
        'total': len(rows), 'M': tally['*'], 'A': tally['+'] + tally['-'],
        'canonical_source_sha256': canonical_rows(rows),
        'all_rows_and_ports_live': True, 'fixed_numeral_roles': len(roles),
    }, duplicates


def changed_form(parent):
    old = parent['source']
    ports = parent['parameters'] + parent['auxiliaries']
    old_ledger, old_duplicates = audit_graph(old, ports, parent['output'], parent['fixed_numeral_recipes'])
    need(old_ledger == parent['ledger'], 'complete parent ledger authentication')
    need((old_ledger['total'], old_ledger['M'], old_ledger['A']) == (243, 129, 114), '243 parent count')
    original = {row[0]: row for row in old}
    fixed = {
        'hist__repunit_factor__50': ['+', 'hist__P__10', 1],
        'hist__range_cell__75': ['-', 'hist__height_slack', 1],
        'hist__range_repunit__76': ['*', 'hist__J__7', 'hist__range_cell__75'],
        'hist__range_mask__77': ['*', 'hist__range_repunit__76', 'hist__repunit_factor__50'],
        'tree_mask_product': ['*', 'hist__P_product__9', 'hist__G12'],
        'tree_mask_sum': ['+', 'hist__J__7', 'tree_mask_product'],
        'tree_mask_shift': ['*', 'hist__P__10', 'tree_mask_sum'],
        'hist__controller_mask__55': ['+', 'hist__J__7', 'tree_mask_shift'],
    }
    for node, tail in fixed.items():
        need(original[node] == [node, *tail], 'exact parent cut row ' + node)
    guards = {
        'hist__repunit_factor__50': ['hist__range_mask__77'],
        'hist__range_cell__75': ['hist__range_repunit__76'],
        'hist__range_repunit__76': ['hist__range_mask__77'],
        'hist__range_mask__77': ['hist__range_mask_region__91'],
        'tree_mask_product': ['tree_mask_sum'],
        'tree_mask_sum': ['tree_mask_shift'],
        'tree_mask_shift': ['hist__controller_mask__55'],
        'hist__controller_mask__55': ['hist__controller_mask_region__90'],
    }
    for node, wanted in guards.items():
        need(consumers(old, node) == wanted, 'complete parent consumer list ' + node)
    replace = {
        'hist__range_repunit__76': ['*', 'hist__J__7', 'hist__repunit_factor__50'],
        'hist__range_mask__77': ['*', 'hist__range_repunit__76', 'hist__range_cell__75'],
        'tree_mask_shift': ['*', 'hist__P__10', 'tree_mask_product'],
        'hist__controller_mask__55': ['+', 'hist__range_repunit__76', 'tree_mask_shift'],
    }
    child = []
    for row in old:
        if row[0] == 'tree_mask_sum':
            continue
        child.append([row[0], *replace[row[0]]] if row[0] in replace else row)
    ledger, new_duplicates = audit_graph(child, ports, parent['output'], parent['fixed_numeral_recipes'])
    need((ledger['total'], ledger['M'], ledger['A']) == (242, 129, 113), '242 child count')
    retained = sum(original[row[0]] == row for row in child)
    need(retained == 238 and len(replace) == 4, '238 retained and four changed records')
    child_guards = {
        'hist__repunit_factor__50': ['hist__range_repunit__76'],
        'hist__range_cell__75': ['hist__range_mask__77'],
        'hist__range_repunit__76': ['hist__controller_mask__55', 'hist__range_mask__77'],
        'hist__range_mask__77': ['hist__range_mask_region__91'],
        'tree_mask_product': ['tree_mask_shift'],
        'tree_mask_shift': ['hist__controller_mask__55'],
        'hist__controller_mask__55': ['hist__controller_mask_region__90'],
    }
    for node, wanted in child_guards.items():
        need(consumers(child, node) == wanted, 'complete child consumer list ' + node)
    need(child[-1] == ['lower_unit_output', '-', 'lower_history_product', 'geo__A'], 'unchanged final subtraction')
    need(len(parent['auxiliaries']) == 43 and len(parent['fixed_numeral_recipes']) == 10, 'witness/role count')
    same_fields = ['parameters', 'auxiliaries', 'domains', 'merged', 'fixed_numeral_recipes',
                   'fixed_u9_recipe', 'output', 'comparisons', 'multiplier_port', 'scaled_factor_semantics']
    result = {key: parent[key] for key in same_fields}
    result.update({
        'source': child, 'ledger': ledger,
        'certificate': {'total': 241, 'M': 129, 'A': 112, 'comparisons': 1, 'positive_witnesses': 43},
        'manual_degree_upper_bound': 936, 'exact_degree_claimed': False,
        'parent_source_sha256': canonical_rows(old),
        'inverse_to_parent': {'all_supplied_coordinates': 'identity'},
        'scope': 'Complete identical polynomial and positive domain; two unchanged mask exits over every commutative ring.',
        'delta': {
            'deleted': [original['tree_mask_sum']], 'added': [],
            'edited': [{'before': original[node], 'after': [node, *tail]} for node, tail in replace.items()],
            'literal_retained_row_records': retained, 'topological_reorder': False,
            'parent_consumer_guards': guards, 'child_consumer_guards': child_guards,
            'fixed_numeral_recipes_changed': False,
        },
        'literal_duplicate_operation_scan': {'parent': old_duplicates, 'child': new_duplicates},
    })
    return result


# Handwritten four-variable commutative-ring calculations; no source graph enters.
def independently_written_cuts():
    def constant(value):
        return {(): value} if value else {}
    def variable(name):
        return {(name,): 1}
    def plus(left, right):
        result = Counter(left)
        result.update(right)
        return {monomial: value for monomial, value in result.items() if value}
    def times(left, right):
        result = Counter()
        for term1, coef1 in left.items():
            for term2, coef2 in right.items():
                result[tuple(sorted(term1 + term2))] += coef1 * coef2
        return dict(result)
    J, P, D, T = [variable(name) for name in ('J', 'P', 'D', 'T')]
    one = constant(1)
    parent_range = times(times(J, D), plus(P, one))
    child_range = times(times(J, plus(P, one)), D)
    parent_controller = plus(J, times(P, plus(J, T)))
    child_controller = plus(times(J, plus(P, one)), times(P, T))
    need(parent_range == child_range, 'independent range-mask cut')
    need(parent_controller == child_controller, 'independent controller-mask cut')
    def serial(poly):
        return [{'monomial': list(mon), 'coefficient': val} for mon, val in sorted(poly.items())]
    return {'variables': ['J', 'P', 'D', 'T'], 'exact_cut_identities': 2,
            'range_common_expansion': serial(parent_range),
            'controller_common_expansion': serial(parent_controller),
            'scope': 'New handwritten cuts only; D and T are independent abstract variables, never computed from saved arrays.'}


def construct_receipt():
    dependencies = []
    old = None
    for name, expected in PINS.items():
        path = SHELF / name
        if not path.exists():
            path = Path('/tmp') / name
        raw = path.read_bytes()
        need(fingerprint(raw) == expected, 'dependency bytes ' + name)
        dependencies.append({'path': str((SHELF / name).relative_to(WORK)), 'bytes': len(raw), 'sha256': expected})
        if name.endswith('.json'):
            old = json.loads(raw)
    need(old is not None and len(old['forms']) == 2, 'two full243 interfaces')
    forms = [changed_form(form) for form in old['forms']]
    need([form['merged'] for form in forms] == [False, True], 'interface ordering')
    return {'status': 'PASS', 'helper_sha256': fingerprint(Path(__file__).read_bytes()),
            'dependencies': dependencies, 'forms': forms,
            'dependency_locator_policy': 'Pinned repository files or identical same-name /tmp files before installation.',
            'handwritten_ring_cuts': independently_written_cuts(),
            'source_arrays_evaluated': False, 'source_degree_propagation': False,
            'predecessor_or_frozen_code_executed_or_imported': False}


def main():
    options = argparse.ArgumentParser()
    options.add_argument('--write', action='store_true')
    request = options.parse_args()
    result = json.dumps(construct_receipt(), sort_keys=True, indent=2) + '\n'
    destination = Path(__file__).with_suffix('.json')
    if request.write:
        destination.write_text(result)
    else:
        need(destination.read_text() == result, 'exact saved receipt')
    print('PASS: two complete242 arrays, static graph checks, two independent handwritten ring cuts')


if __name__ == '__main__':
    main()
