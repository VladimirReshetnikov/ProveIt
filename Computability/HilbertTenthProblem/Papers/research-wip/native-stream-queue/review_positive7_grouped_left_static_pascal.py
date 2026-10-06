"""Original inert-record auditor. Never evaluates a saved arithmetic operation."""
from pathlib import Path
import hashlib
import json
import traceback

BASE = Path('/tmp')
RESULT = BASE / 'review_positive7_grouped_left_static_pascal.json'
if RESULT.exists():
    raise RuntimeError('First-result file exists: this auditor must never be replayed.')
PINS = {
    'positive7_grouped_left_compiler_riemann.md': '4987ae06163aa35dd138ce616873cc7804852273aefaa3faedac32de756f299e',
    'positive7_grouped_left_compiler_riemann_provenance.json': 'de063ab37097c93bfff7c773d026f5f8cb981c9a5c68c77d37252a8055fc21fd',
    'positive7_grouped_right_compiler_riemann.json': '4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c',
    'positive7_grouped_left_compiler_riemann.json': 'f247d5f4b7f04a0fe14847b9dfe5db46c60b002c709dde71fd248e306868d8d1',
    'positive7_grouped_left_compiler_riemann.py': '7d2d4bb215633afc340068a43913eb80b7396d3baa7427d2a3f8df679a0622af',
    'positive7_grouped_left_compiler_riemann_first_run.txt': 'c996faafb6c09939cd63baed9237fccd1b26c943d97f1a11619c765425ebcc06',
    'positive7_grouped_left_shared_tail_riemann.md': 'a555ae04bfeb8d9ca3dbbf5bdb7551b22f7e2390d41d88050cf1cfaef4e9479f',
}
REPORT = {'status': 'STARTED', 'scope': 'Original metadata-only all-row audit; no source values or degrees computed.',
          'auditor_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'inputs': [], 'examples': []}


def require(test, message):
    if not test:
        raise AssertionError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def compact(rows):
    return sha(json.dumps(rows, separators=(',', ':'), ensure_ascii=False).encode())


def census(rows):
    require(all(len(row) == 4 and row[1] in ('+', '-', '*') for row in rows), 'row grammar')
    mult = sum(row[1] == '*' for row in rows)
    return {'M': mult, 'A': len(rows) - mult, 'operations': len(rows)}


def strings(obj, path=()):
    if isinstance(obj, str):
        yield path, obj
    elif isinstance(obj, list):
        for i, value in enumerate(obj):
            yield from strings(value, path + (i,))
    elif isinstance(obj, dict):
        for key, value in obj.items():
            yield from strings(value, path + (key,))


def stage_slices(example):
    result, cursor = {}, 0
    for label, count in example['stages'].items():
        end = cursor + count['operations']
        part = example['source'][cursor:end]
        require(census(part) == count, 'stage census ' + label)
        result[label] = part
        cursor = end
    require(cursor == len(example['source']), 'stages exhaust source')
    return result


def check_graph(example):
    supplied = example['ordinary_parameters'] + example['positive_auxiliaries']
    require(len(supplied) == len(set(supplied)), 'supplied names distinct')
    known, edges, roles = set(supplied), {}, {}
    for name, operation, first, second in example['source']:
        require(isinstance(name, str) and name not in known, 'unique output ' + str(name))
        dependencies = []
        for operand in (first, second):
            if isinstance(operand, str):
                require(operand in known, 'operand available: ' + name + ' uses ' + operand)
                dependencies.append(operand)
            elif isinstance(operand, dict):
                require(set(operand) == {'fixed'}, 'fixed role descriptor')
                role = operand['fixed']
                require(role not in roles, 'role used once ' + role)
                roles[role] = [name, operation]
            else:
                require(type(operand) is int, 'literal integer operand')
        known.add(name)
        edges[name] = dependencies
    reached, frontier = set(), [example['output']]
    while frontier:
        value = frontier.pop()
        if value not in reached:
            reached.add(value)
            frontier.extend(edges.get(value, []))
    require(reached == known, 'all supplied and computed registers live')
    r = example['r']
    expected = {'K', 'alpha', 'gamma', 'center_lambda', 'guard_bound', 'kappa_minus_one'}
    for j in range(r):
        expected.update(f'form_basis_u_{j}_{i}' for i in (1, 2))
        expected.update(f'form_basis_v_{j}_{i}' for i in (1, 2, 3))
        expected.update(f'quotient_T_{j}_{i}_{k}' for i in (1, 2) for k in (1, 2))
        expected.update(f'relator_E_{8+2*j}_{i}_{k}' for i in (4, 5, 6) for k in (1, 2))
    require(set(roles) == expected and len(roles) == 6+15*r, 'linked fixed-role family')
    require(roles['gamma'] == ['program_tau', '+'], 'gamma exception')
    require(all(role == 'gamma' or use[1] == '*' for role, use in roles.items()), 'remaining roles multiply')
    require(example['static_checks'] == {'topology': True, 'all_computed_live': True,
            'all_supplied_live': True, 'named_fixed_roles': sorted(expected)}, 'independent static checks')
    for field in ('ports', 'comparisons', 'centered_input_forms', 'lanes_in_order',
                  'selected_center_ports', 'parent_suffix_bindings', 'quotient_pair_ports'):
        for path, value in strings(example[field]):
            require(value in known, 'active binding ' + field + str(path))
    return {'computed': len(edges), 'supplied': len(supplied), 'roles': roles}


def audit():
    loaded = {}
    for filename, pin in PINS.items():
        data = (BASE / filename).read_bytes()
        require(sha(data) == pin, 'input hash ' + filename)
        REPORT['inputs'].append({'path': str(BASE / filename), 'sha256': pin, 'bytes': len(data)})
        if filename.endswith('.json'):
            loaded[filename] = json.loads(data)
    parent = loaded['positive7_grouped_right_compiler_riemann.json']
    child = loaded['positive7_grouped_left_compiler_riemann.json']
    provenance = loaded['positive7_grouped_left_compiler_riemann_provenance.json']
    require(provenance['artifact']['sha256'] == PINS['positive7_grouped_left_compiler_riemann.md'], 'frozen primary sidecar binding')
    require(set(child) == set(parent), 'outer receipt key set')
    require(child['fixed_data_recipe'] == parent['fixed_data_recipe'], 'entire fixed recipe literal')
    require(child['r0_fallback'] == parent['r0_fallback'], 'entire r0 fallback literal')
    require(child['r0_fallback']['polynomial_operations'] == 903 and
            child['r0_fallback']['positive_witnesses'] == 96, 'r0 stated boundary')
    require(child['emitter_sha256'] == PINS['positive7_grouped_left_compiler_riemann.py'], 'emitter binding')
    require(child['local_proof_sha256'] == PINS['positive7_grouped_left_shared_tail_riemann.md'], 'local proof binding')
    require(child['inputs'] == [{'path': str(BASE / 'positive7_grouped_right_compiler_riemann.json'),
            'sha256': PINS['positive7_grouped_right_compiler_riemann.json'],
            'bytes': (BASE / 'positive7_grouped_right_compiler_riemann.json').stat().st_size}], 'sole parent input')
    require([e['r'] for e in child['examples']] == [1, 2, 4] == [e['r'] for e in parent['examples']], 'fixture order')
    formulas = {
        'uniform_certificate': '(196+27r+gM-A-B-D18-E24)M+(463+40r+gA-B)A',
        'uniform_polynomial': '(219+27r+gM-A-B-D18-E24)M+(508+40r+gA-B)A',
        'uniform_operations': '727+67r+gM+gA-A-2B-D18-E24',
        'collected_certificate': '(199+27r+gM-A-B-D18-E24-eta)M+(467+39r+gA-B-eta)A',
        'collected_polynomial': '(222+27r+gM-A-B-D18-E24-eta)M+(512+39r+gA-B-eta)A',
        'collected_operations': '734+66r+gM+gA-A-2B-D18-E24-2eta',
        'witnesses': '96+6r', 'equations': 23, 'fixed_roles': '6+15r; gamma is the unique addition role'}
    for key, value in formulas.items():
        require(child['generic_ledger'][key] == value, 'hand-derived generic formula ' + key)
    totals = {'unmoved': 0, 'moved': 0, 'inserted': 0, 'removed': 0, 'rows': 0}
    for old, new in zip(parent['examples'], child['examples']):
        r = old['r']; oldrows = old['source']; newrows = new['source']
        # These exact fixture aliases come from inert reads of the paid interface.
        P4 = 'left_support_P4' if r == 2 else 'geom_P4'
        U2 = 'left_pair_factor_2' if r == 2 else 'geom_factor_4'
        U6 = 'geom_factor_12' if r == 2 else 'left_pair_factor_6'
        byname = {row[0]: row for row in oldrows}
        P12 = 'geom_P12' if r == 2 else 'left_support_P12'
        Pm = f'geom_P{8+2*r}'
        require(old['ports']['left_support_P12'] == P12 and old['ports']['selector_power'] == Pm, 'power port aliases')
        require(byname[P4][1:] == ['*', 'scale_square_0', 'scale_square_0'], 'P4 paid producer')
        require(byname[U2][1:] == ['+', 1, 'scale_square_0'] or
                byname[U2][1:] == ['+', 'scale_square_0', 1], 'U2 paid meaning')
        require(byname[U6][1:] == ['+', 1, 'pack_P6'] or
                byname[U6][1:] == ['+', 'pack_P6', 1], 'U6 paid meaning')
        oldcut = []; high = 'left_high_tail'
        for j in reversed(range(r)):
            stem = f'left_form_'; rep = stem+f'repeated_{j}'; shift = stem+f'high_shift_{j}'; join = stem+f'high_join_{j}'
            oldcut.extend([[rep, '*', U2, f'left_form_pair_{j}'], [shift, '*', P4, high], [join, '+', shift, rep]])
            high = join
        oldcut.extend([
            ['left_seven_repeated', '*', 'left_four_seven_factor', 'left_history_join_1'],
            ['left_seven_high_shift', '*', 'left_support_P28', high],
            ['left_seven_high_join', '+', 'left_seven_high_shift', 'left_seven_repeated'],
            ['left_six_repeated_b', '*', U6, 'left_short_history_b'],
            ['left_six_high_shift_b', '*', P12, 'left_seven_high_join'],
            ['left_six_high_join_b', '+', 'left_six_high_shift_b', 'left_six_repeated_b'],
            ['left_six_repeated_a', '*', U6, 'left_history_join_2'],
            ['left_six_high_shift_a', '*', P12, 'left_six_high_join_b'],
            ['left_six_high_join_a', '+', 'left_six_high_shift_a', 'left_six_repeated_a']])
        moving = [['group_right_P24', '*', P12, P12]]
        if r == 1:
            moving.append(['group_right_tail_power', '*', 'left_support_P28', 'left_support_P28'])
        elif r == 2:
            moving.extend([['group_right_m18', '*', 'left_support_P28', 'scale_square_0'],
                           ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']])
        else:
            moving.extend([['group_right_P18', '*', P12, 'pack_P6'], ['group_right_m18', '*', Pm, 'group_right_P18'],
                           ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']])
        inserted = []; qword = f'left_form_pair_{r-1}'
        for j in range(r-2, -1, -1):
            mul = f'left_group_q_mul_{j}'; add = f'left_group_q_add_{j}'
            inserted.extend([[mul, '*', qword, P4], [add, '+', mul, f'left_form_pair_{j}']]); qword = add
        inserted.extend([
            ['left_group_forms_repeat', '*', U2, qword],
            ['left_group_forms_shift', '*', 'left_support_P28', 'left_group_forms_repeat'],
            ['left_group_seven', '*', 'left_four_seven_factor', 'left_history_join_1'],
            ['left_group_upper_sum', '+', 'left_group_seven', 'left_group_forms_shift'],
            ['left_group_upper', '*', 'group_right_P24', 'left_group_upper_sum'],
            ['left_group_six_shift', '*', P12, 'left_short_history_b'],
            ['left_group_lower_sum', '+', 'left_history_join_2', 'left_group_six_shift'],
            ['left_group_lower', '*', U6, 'left_group_lower_sum'],
            ['left_group_tail', '*', 'group_right_tail_power', 'left_high_tail'],
            ['left_group_partial', '+', 'left_group_lower', 'left_group_upper'],
            ['left_six_high_join_a', '+', 'left_group_partial', 'left_group_tail']])
        removed = {row[0] for row in oldcut}; moved = {row[0] for row in moving}; exit_name = 'left_six_high_join_a'
        require([x for x in oldrows if x[0] in removed] == oldcut, 'entire old cone')
        require([x for x in oldrows if x[0] in moved] == moving, 'literal support producers')
        require(census(oldcut) == {'M': 2*r+6, 'A': r+3, 'operations': 3*r+9}, 'old cut count')
        require(census(inserted) == {'M': r+6, 'A': r+3, 'operations': 2*r+9}, 'new cut count')
        expected = []; unmoved = []
        for record in oldrows:
            if record[0] == 'left_high_tail_shift': expected.extend(moving)
            if record[0] not in removed | moved: expected.append(record); unmoved.append(record)
            if record[0] == exit_name: expected.extend(inserted)
        require(newrows == expected, 'all successor records equal independent grammar')
        external = [x for x in oldrows if x[0] not in removed and any(isinstance(y, str) and y in removed for y in x[2:])]
        require(external == [['left_selector_shift', '*', exit_name, Pm]], 'sole external arithmetic consumer')
        mentions = [[list(path), value] for path, value in strings(old)
                    if value in removed and path[0] not in ('source', 'grouped_right_splice')]
        require(mentions == [[['ports', 'high_left_pack'], exit_name]], 'sole active metadata exit')
        left_label = 'grouped_high_left_pack_with_shared_powers'
        before, after = stage_slices(old), stage_slices(new)
        require(list(after) == [left_label if x == 'repeated_high_left_pack' else x for x in before], 'stage order')
        for label, part in before.items():
            dest = left_label if label == 'repeated_high_left_pack' else label
            expected_part = []
            for record in part:
                if record[0] == 'left_high_tail_shift': expected_part.extend(moving)
                if record[0] not in removed | moved: expected_part.append(record)
                if record[0] == exit_name: expected_part.extend(inserted)
            require(after[dest] == expected_part, 'every stage record ' + dest)
        require(newrows[-68:] == oldrows[-68:] and after['complete_native64'] == before['complete_native64'], 'literal native/finalizer')
        M, A = {1: (247, 551), 2: (273, 589), 4: (332, 671)}[r]
        require(census(newrows) == new['polynomial_ledger'] == {'M': M, 'A': A, 'operations': M+A}, 'full ledger')
        require(census(newrows[:-68]) == new['certificate_ledger'] == {'M': M-23, 'A': A-45, 'operations': M+A-68}, 'certificate ledger')
        require(new['certificate_prefix_rows'] == len(newrows)-68, 'certificate prefix')
        changed = {'source','stages','polynomial_ledger','certificate_ledger','certificate_prefix_rows',
                   'grouped_right_splice','grouped_left_splice','grouped_right_support_products',
                   'joint_right_native_products','shared_left_right_support_products','joint_pack_native_products'}
        require(set(new) == (set(old)-{'grouped_right_splice','grouped_right_support_products','joint_right_native_products'}) |
                {'grouped_left_splice','shared_left_right_support_products','joint_pack_native_products'}, 'exact fixture key set')
        require({key for key in set(old) | set(new) if old.get(key) != new.get(key)} == changed, 'exact metadata change set')
        require(new['shared_left_right_support_products'] == len(moving) and new['joint_pack_native_products'] == len(moving)+1, 'paid support counters')
        require(new['native_scale_products'] == 1 and len(new['positive_auxiliaries']) == 96+6*r, 'native and witness scope')
        require(new['m'] == 8+2*r and new['ell'] == 62+6*r and new['equations'] == 23, 'inherited shape')
        require(new['witnesses'] == 96+6*r and new['selected_ports'] == 52+4*r and len(new['comparisons']) == 23, 'supplied lane/comparison counts')
        splice = new['grouped_left_splice']
        for key, value in {'removed_rows': oldcut, 'inserted_rows': inserted, 'moved_literal_rows': moving,
                           'unmoved_literal_row_names': [x[0] for x in unmoved], 'old_cut_ledger': census(oldcut),
                           'new_cut_ledger': census(inserted), 'preserved_exit': exit_name,
                           'external_consumer_rows': external, 'preserved_active_mentions': mentions,
                           'rewritten_outside_rows': [], 'source_sha256_before': compact(oldrows),
                           'source_sha256_after': compact(newrows), 'support_insertion_before': 'left_high_tail_shift',
                           'new_cone_insertion_at_old_exit': exit_name, 'changed_top_level_fields': sorted(changed),
                           'parent_receipt_sha256': PINS['positive7_grouped_right_compiler_riemann.json'],
                           'local_proof_sha256': PINS['positive7_grouped_left_shared_tail_riemann.md']}.items():
            require(splice[key] == value, 'splice metadata ' + key)
        require(not any(value in removed-{exit_name} for path, value in strings(new)
                        if path[0] not in ('source', 'grouped_left_splice')), 'no stale active bindings')
        graph = check_graph(new)
        partition = {'unmoved': len(unmoved), 'moved': len(moving), 'inserted': len(inserted), 'removed': len(oldcut), 'rows': len(newrows)}
        require(partition == {1: {'unmoved':785,'moved':2,'inserted':11,'removed':12,'rows':798},
                              2: {'unmoved':846,'moved':3,'inserted':13,'removed':15,'rows':862},
                              4: {'unmoved':982,'moved':4,'inserted':17,'removed':21,'rows':1003}}[r], 'disjoint fixture partition')
        for key in totals: totals[key] += partition[key]
        REPORT['examples'].append({'r': r, 'partition': partition, 'ledger': census(newrows),
                                   'source_sha256': compact(newrows), 'stage_checks': list(after), 'graph': graph})
    require(totals == {'unmoved':2613,'moved':9,'inserted':41,'removed':48,'rows':2663}, 'whole partition')
    REPORT['totals'] = totals
    REPORT['status'] = 'PASS: all2663 records, exact replacement and metadata; no arithmetic evaluation'


try:
    audit()
except Exception:
    REPORT['status'] = 'FAIL: first result retained permanently'
    REPORT['error'] = traceback.format_exc()
    RESULT.write_text(json.dumps(REPORT, indent=2) + '\n')
    raise
else:
    RESULT.write_text(json.dumps(REPORT, indent=2) + '\n')
    print(REPORT['status'])
