#!/usr/bin/env python3
"""Fresh independent static comparison. No source values or degrees are computed."""
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
AUTHOR = Path('/tmp/neary_woods_positive_first_production247_tesla')
SELF = Path(__file__)
PINS = {
    str(AUTHOR.with_suffix('.md')): '9cb9da3c211fecbe3129421b23a16c747d8d1bf7b6365cf6320c426733ffd56a',
    str(AUTHOR.with_suffix('.py')): 'db9ecad324c6082f6c734cfe7fb55fc64a9d4e76920b2bff2127775d1392c771',
    str(AUTHOR.with_suffix('.json')): '85e91368ddb3b4764879cd8591d730a60ed95e569026ec8ad7a0b6600739968e',
    str(BASE / 'neary_woods_positive_upper248_tesla.md'): 'f3329cf28090e39a219ac4e3d8882b99fc5bab72ae0507647a193cbdb514d557',
    str(BASE / 'neary_woods_positive_upper248_tesla.json'): 'bab6ba8d61e9fac494ca42124b043c358597d19bf1ebf8f8699b2c054ff476bc',
}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def canonical(data):
    return digest(json.dumps(data, sort_keys=True, separators=(',', ':')).encode())

def operand_key(value):
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        require(set(value) == {'fixed_numeral'}, 'unrecognized literal operand')
        return '@' + value['fixed_numeral']
    require(type(value) is int, 'noninteger literal')
    return None

DELETED = 'hist__repunit_tail__64'
REPLACEMENTS = {
    'hist__global_sum__13': ['+', 'hist__ZV0', 'hist__global_sum__12'],
    'hist__linear1_coefficient__27': ['*', 'hist__ZV0', {'fixed_numeral': 'lower_difference'}],
    'hist__linear1_coefficient__29': ['*', 'hist__S0', {'fixed_numeral': 'production_offset'}],
    'hist__linear_group__164': ['+', 'hist__S0', 'hist__Shat3'],
    'hist__J__7': ['-', 'hist__selector_sum__6', 3],
    'hist__pack_sum__61': ['+', 'hist__S0', 'hist__pack_product__60'],
    'hist__pack_sum__71': ['+', 'hist__ZV0', 'hist__pack_product__70'],
    'hist__unhat_pack__74': ['-', 'hist__pack_sum__73', 'hist__P2__51'],
    'hist__unhat_pack__65': ['-', 'hist__pack_sum__63', 'hist__P2__51'],
}
CUT = {
    'hist__P__10', 'hist__J__7', 'hist__unhat_pack__65',
    'hist__unhat_pack__74', 'hist__linear_constant__168',
    'hist__linear_constant__173',
}
FACTOR_NAMES = [
    'geo__R15', 'geo__P17', 'geo__first_unit',
    'and__R15', 'and__P17', 'and__first_unit',
    'geo__f_square_minus_one', 'and__f_square_minus_one',
    'geo__index_unit', 'and__index_unit',
    'geo__linear_unit', 'and__linear_unit',
    'mask_repunit_unit', 'history_upper_unit',
    'history_global_unit', 'lower_history_unit',
]
CONSUMERS = {
    'hist__Shat0': {'hist__linear1_coefficient__29', 'hist__linear_group__164', 'hist__pack_sum__61'},
    'hist__ZVhat0': {'hist__global_sum__13', 'hist__linear1_coefficient__27', 'hist__pack_sum__71'},
    'hist__global_bound': {'hist__P__10'},
    DELETED: {'hist__unhat_pack__65', 'hist__unhat_pack__74'},
    '@upper_constant': {'hist__linear_constant__168'},
    '@lower_constant': {'hist__linear_constant__173'},
}

def static_graph(form):
    rows = form['source']
    parameters = form['parameters']
    witnesses = form['auxiliaries']
    roles = form['fixed_numeral_recipes']
    free = set(parameters + witnesses)
    require(len(free) == len(parameters) + len(witnesses), 'duplicate free port')
    known = free | {'@' + k for k in roles}
    graph = {}
    users = collections.defaultdict(set)
    operators = collections.Counter()
    for line, record in enumerate(rows, 1):
        require(len(record) == 4 and record[1] in ('+', '-', '*'), 'row format')
        name = record[0]
        require(isinstance(name, str) and name not in known, 'duplicate producer')
        predecessors = {operand_key(arg) for arg in record[2:]} - {None}
        require(predecessors <= known, 'forward/unknown operand at row ' + str(line))
        graph[name] = predecessors
        for prior in predecessors:
            users[prior].add(name)
        known.add(name)
        operators[record[1]] += 1
    live, todo = set(), [form['output']]
    while todo:
        node = todo.pop()
        if node in live:
            continue
        live.add(node)
        todo.extend(graph.get(node, ()))
    require(live == known, 'dead row, free port or fixed role')
    return graph, users, {
        'rows': len(rows), 'multiplications': operators['*'],
        'additions_and_subtractions': operators['+'] + operators['-'],
        'parameters_including_input': len(parameters), 'positive_witnesses': len(witnesses),
        'live_fixed_roles': len(roles), 'all_rows_ports_roles_live': True,
        'canonical_source_sha256': canonical(rows),
    }

def stop_at_cut(users, seeds):
    pending, visited, exits = list(seeds), set(), set()
    while pending:
        node = pending.pop()
        if node in CUT:
            exits.add(node)
            continue
        if node in visited:
            continue
        visited.add(node)
        require(bool(users[node]), 'changed cone terminates before its claimed cut: ' + node)
        pending.extend(users[node])
    require(exits == CUT, 'six exits not exactly recovered')
    return {'internal_nodes_including_changed_inputs': sorted(visited), 'exits': sorted(exits)}

def product_spine(rows):
    by_name = {r[0]: r for r in rows}
    leaves, branch_nodes = [], []
    def visit(node):
        if node in FACTOR_NAMES:
            leaves.append(node)
            return
        require(node in by_name, 'unknown product node')
        row = by_name[node]
        require(row[1] == '*' and all(isinstance(a, str) for a in row[2:]), 'nonproduct spine row')
        branch_nodes.append(node)
        visit(row[2])
        visit(row[3])
    visit('lower_history_product')
    require(collections.Counter(leaves) == collections.Counter(FACTOR_NAMES), '16 factor multiplicities')
    require(len(branch_nodes) == len(set(branch_nodes)) == 15, '15 product multiplications')
    return {'factor_leaves': leaves, 'multiplication_nodes': branch_nodes}

def inspect(parent, child):
    pgraph, pusers, pstats = static_graph(parent)
    cgraph, cusers, cstats = static_graph(child)
    before, after = parent['source'], child['source']
    before_by_name = {r[0]: r for r in before}
    require(before_by_name[DELETED] == [DELETED, '+', 'hist__P2__51', 'hist__P__10'], 'deleted expression')
    expected = []
    for row in before:
        if row[0] == DELETED:
            continue
        expected.append([row[0]] + REPLACEMENTS[row[0]] if row[0] in REPLACEMENTS else row)
    require(after == expected, 'complete ordered source mismatch')
    edited = [{'name': r[0], 'before': before_by_name[r[0]], 'after': r} for r in after if r != before_by_name[r[0]]]
    require(len(edited) == 9 and len(after) - len(edited) == 238, 'literal delta count')
    require((pstats['rows'], pstats['multiplications'], pstats['additions_and_subtractions']) == (248, 129, 119), 'parent cost')
    require((cstats['rows'], cstats['multiplications'], cstats['additions_and_subtractions']) == (247, 129, 118), 'child cost')
    require(cstats['positive_witnesses'] == 43 and cstats['live_fixed_roles'] == 11, 'child interface')
    for field in ('parameters', 'domains', 'merged', 'fixed_u9_recipe', 'output', 'comparisons', 'multiplier_port', 'scaled_factor_semantics'):
        require(parent[field] == child[field], 'changed inherited interface ' + field)
    names = {'hist__Shat0': 'hist__S0', 'hist__ZVhat0': 'hist__ZV0'}
    require([names.get(w, w) for w in parent['auxiliaries']] == child['auxiliaries'], 'witness list')
    recipe_delta = {k: [parent['fixed_numeral_recipes'][k], child['fixed_numeral_recipes'][k]] for k in parent['fixed_numeral_recipes'] if parent['fixed_numeral_recipes'][k] != child['fixed_numeral_recipes'][k]}
    require(recipe_delta == {'upper_constant': ['2^(beta+2)+4', '2^(beta+2)+3'], 'lower_constant': ['2^L+production_offset+10', '12']}, 'exact numeral changes')
    require(parent['fixed_numeral_recipes']['lower_difference'] == child['fixed_numeral_recipes']['lower_difference'] == '2^L-2', 'lower compensation recipe')
    for node, targets in CONSUMERS.items():
        require(pusers[node] == targets, 'unlisted parent consumer: ' + node)
    parent_cone = stop_at_cut(pusers, set(CONSUMERS))
    child_cone = stop_at_cut(cusers, {'hist__S0', 'hist__ZV0', 'hist__global_bound', '@upper_constant', '@lower_constant'})
    require('hist__range_mask__77' in cusers['hist__repunit_factor__50'], 'lost live P+1')
    require(after[-1] == ['lower_unit_output', '-', 'lower_history_product', 'geo__A'], 'final output')
    require(child['comparisons'] == [['lower_history_product', 'geo__A']], 'certificate comparison')
    require(all(next(r for r in after if r[0] == n) == before_by_name[n] for n in FACTOR_NAMES), 'factor producer changed')
    spine = product_spine(after)
    require(spine == product_spine(before), 'changed factor product spine')
    return {
        'merged_duration_parameter': child['merged'], 'parent_static': pstats, 'child_static': cstats,
        'certificate_before_final_subtraction': {'rows': 246, 'M': 129, 'A': 117, 'comparisons': 1},
        'delta': {'edited': edited, 'deleted': before_by_name[DELETED], 'literal_retained_rows': 238,
                  'new_rows': 0, 'same_order_after_deletion': True, 'fixed_recipes': recipe_delta},
        'exact_parent_consumers': {k: sorted(v) for k, v in CONSUMERS.items()},
        'parent_changed_cones': parent_cone, 'child_changed_cones': child_cone,
        'unchanged_six_cut_exit_names': sorted(CUT), 'unchanged_factor_spine': spine,
        'degree_not_computed': True,
    }

def main():
    authenticated = []
    for name, pin in PINS.items():
        data = Path(name).read_bytes()
        require(digest(data) == pin, 'input hash: ' + name)
        authenticated.append({'path': name, 'sha256': pin, 'bytes': len(data)})
    child = json.loads(AUTHOR.with_suffix('.json').read_text())
    parent = json.loads((BASE / 'neary_woods_positive_upper248_tesla.json').read_text())
    require(len(child['forms']) == len(parent['forms']) == 2, 'number of forms')
    dependencies = []
    for item in child['dependencies']:
        data = (ROOT / item['path']).read_bytes()
        require(digest(data) == item['sha256'] and len(data) == item['bytes'], 'dependency byte binding')
        dependencies.append(item)
    results = [inspect(a, b) for a, b in zip(parent['forms'], child['forms'])]
    require([r['merged_duration_parameter'] for r in results] == [False, True], 'form order')
    rows0, rows1 = (f['source'] for f in child['forms'])
    unequal = [(i + 1, a, b) for i, (a, b) in enumerate(zip(rows0, rows1)) if a != b]
    require(unequal == [(1, ['program_duration_bound', '+', 'program_bound', 'program_duration_gap'],
                        ['program_duration_bound', '+', 'program_E', 'program_duration_gap'])], 'only interface row difference')
    result = {
        'status': 'PASS within static-source and handwritten cut scope',
        'reviewer_helper_sha256': digest(SELF.read_bytes()), 'authenticated_inputs': authenticated,
        'author_dependency_pins_independently_authenticated': dependencies, 'forms': results,
        'totals': {'child_rows_inspected': 494, 'parent_rows_compared': 496, 'child_arrays': 2,
                   'literal_retained_records': 476, 'edited_records': 18, 'deleted_records': 2},
        'between_interface_difference': unequal,
        'scope': {'saved_array_evaluation': False, 'saved_array_degree_propagation': False,
                  'author_or_predecessor_execution_or_import': False,
                  'new_independent_complete_native_proof_audit': False,
                  'full_author_md_and_py_read_inertly': True,
                  'six_changed_cut_identities_challenged_by_hand': True},
    }
    print(json.dumps(result, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
