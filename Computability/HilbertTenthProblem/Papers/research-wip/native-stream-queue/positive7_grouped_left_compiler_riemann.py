"""Original one-run metadata composer. Stored arithmetic records are never evaluated."""
from pathlib import Path
import hashlib
import json
from collections import Counter

PARENT = Path('/tmp/positive7_grouped_right_compiler_riemann.json')
PARENT_PIN = '4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c'
LOCAL = Path('/tmp/positive7_grouped_left_shared_tail_riemann.md')
LOCAL_PIN = 'a555ae04bfeb8d9ca3dbbf5bdb7551b22f7e2390d41d88050cf1cfaef4e9479f'
DESTINATION = Path('/tmp/positive7_grouped_left_compiler_riemann.json')
assert not DESTINATION.exists(), 'One lifetime run only: never overwrite a first receipt.'
sha = lambda data: hashlib.sha256(data).hexdigest()
parent_bytes = PARENT.read_bytes()
assert sha(parent_bytes) == PARENT_PIN
assert sha(LOCAL.read_bytes()) == LOCAL_PIN
parent = json.loads(parent_bytes)
assert [entry['r'] for entry in parent['examples']] == [1, 2, 4]


def ledger(records):
    labels = Counter(record[1] for record in records)
    assert set(labels) <= {'+', '-', '*'}
    mult = labels['*']
    add = labels['+'] + labels['-']
    return {'M': mult, 'A': add, 'operations': mult + add}


def digest(records):
    return sha(json.dumps(records, separators=(',', ':'), ensure_ascii=False).encode())


def text_leaves(value, trail=()):
    if isinstance(value, str):
        yield trail, value
    elif isinstance(value, list):
        for index, item in enumerate(value):
            yield from text_leaves(item, trail + (index,))
    elif isinstance(value, dict):
        for key, item in value.items():
            yield from text_leaves(item, trail + (key,))


children = []
for old in parent['examples']:
    r = old['r']
    rows = old['source']
    lookup = {row[0]: row for row in rows}
    assert len(lookup) == len(rows)
    ports = old['ports']
    P, Pm = ports['P'], ports['selector_power']
    P12 = ports['left_support_P12']
    P4 = lookup['left_form_high_shift_0'][2]
    U2 = lookup['left_form_repeated_0'][2]
    U6 = lookup['left_six_repeated_a'][2]
    assert lookup['left_high_tail_shift'] == ['left_high_tail_shift', '*', 'digit_height', P]
    assert lookup['left_high_tail'] == ['left_high_tail', '+', 'left_high_tail_shift', ports['S']]
    assert not any(name.startswith('common_center_restored') for name in lookup)

    # Specify the entire removed cone as literal records, independently of its row positions.
    old_cone = []
    accumulator = 'left_high_tail'
    for j in range(r - 1, -1, -1):
        repeated = f'left_form_repeated_{j}'
        shifted = f'left_form_high_shift_{j}'
        joined = f'left_form_high_join_{j}'
        old_cone += [[repeated, '*', U2, f'left_form_pair_{j}'],
                     [shifted, '*', P4, accumulator], [joined, '+', shifted, repeated]]
        accumulator = joined
    old_cone += [
        ['left_seven_repeated', '*', 'left_four_seven_factor', 'left_history_join_1'],
        ['left_seven_high_shift', '*', 'left_support_P28', accumulator],
        ['left_seven_high_join', '+', 'left_seven_high_shift', 'left_seven_repeated'],
        ['left_six_repeated_b', '*', U6, 'left_short_history_b'],
        ['left_six_high_shift_b', '*', P12, 'left_seven_high_join'],
        ['left_six_high_join_b', '+', 'left_six_high_shift_b', 'left_six_repeated_b'],
        ['left_six_repeated_a', '*', U6, 'left_history_join_2'],
        ['left_six_high_shift_a', '*', P12, 'left_six_high_join_b'],
        ['left_six_high_join_a', '+', 'left_six_high_shift_a', 'left_six_repeated_a']]
    cut_names = {row[0] for row in old_cone}
    assert [row for row in rows if row[0] in cut_names] == old_cone
    assert ledger(old_cone) == {'M': 2*r+6, 'A': r+3, 'operations': 3*r+9}
    external = [row for row in rows if row[0] not in cut_names and
                any(isinstance(arg, str) and arg in cut_names for arg in row[2:])]
    assert external == [['left_selector_shift', '*', 'left_six_high_join_a', Pm]]
    mentions = [(list(path), name) for path, name in text_leaves(old)
                if name in cut_names and path[0] not in {'source', 'grouped_right_splice'}]
    assert mentions == [(['ports', 'high_left_pack'], 'left_six_high_join_a')]

    # These fixture-specific products remain paid and are MOVED, never duplicated.
    support = [['group_right_P24', '*', P12, P12]]
    if r == 1:
        support += [['group_right_tail_power', '*', 'left_support_P28', 'left_support_P28']]
    elif r == 2:
        support += [['group_right_m18', '*', 'left_support_P28', 'scale_square_0'],
                    ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']]
    else:
        assert r == 4
        support += [['group_right_P18', '*', P12, 'pack_P6'],
                    ['group_right_m18', '*', Pm, 'group_right_P18'],
                    ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']]
    moved_names = {row[0] for row in support}
    assert not (moved_names & cut_names)
    assert [row for row in rows if row[0] in moved_names] == support
    assert support == old['grouped_right_splice']['shared_support_rows']
    assert len(support) == {1: 2, 2: 3, 4: 4}[r]

    new_cone = []
    qword = f'left_form_pair_{r-1}'
    for j in range(r-2, -1, -1):
        product = f'left_group_q_mul_{j}'
        joined = f'left_group_q_add_{j}'
        new_cone += [[product, '*', qword, P4], [joined, '+', product, f'left_form_pair_{j}']]
        qword = joined
    new_cone += [
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
        ['left_six_high_join_a', '+', 'left_group_partial', 'left_group_tail']]
    assert ledger(new_cone) == {'M': r+6, 'A': r+3, 'operations': 2*r+9}
    assert {row[0] for row in new_cone} & set(lookup) == {'left_six_high_join_a'}

    stage_parts = {}
    cursor = 0
    for stage, counts in old['stages'].items():
        part = rows[cursor:cursor + counts['operations']]
        assert ledger(part) == counts
        stage_parts[stage] = part
        cursor += len(part)
    assert cursor == len(rows)
    assert set(row[0] for row in stage_parts['repeated_high_left_pack']) >= cut_names
    assert set(row[0] for row in stage_parts['grouped_right_pack_and_joins']) >= moved_names
    assembled = []
    new_stages = {}
    unmoved_literal = []
    for stage, part in stage_parts.items():
        changed_part = []
        for row in part:
            if row[0] == 'left_high_tail_shift':
                changed_part.extend(support)
            if row[0] not in cut_names | moved_names:
                changed_part.append(row)
                unmoved_literal.append(row[0])
            if row[0] == 'left_six_high_join_a':
                changed_part.extend(new_cone)
        destination_stage = ('grouped_high_left_pack_with_shared_powers'
                             if stage == 'repeated_high_left_pack' else stage)
        new_stages[destination_stage] = ledger(changed_part)
        assembled.extend(changed_part)
    assert len(unmoved_literal) + len(support) + len(new_cone) == len(assembled)
    assert len(assembled) == len(rows) - r
    assert assembled[-68:] == rows[-68:]
    assert ledger(assembled) == {1: {'M':247,'A':551,'operations':798},
                                2: {'M':273,'A':589,'operations':862},
                                4: {'M':332,'A':671,'operations':1003}}[r]
    assert new_stages['complete_native64'] == old['stages']['complete_native64']
    assert new_stages['native_scale_from_right_tail_power'] == old['stages']['native_scale_from_right_tail_power']

    supplied = set(old['ordinary_parameters'] + old['positive_auxiliaries'])
    assert len(old['positive_auxiliaries']) == 96+6*r
    available = set(supplied)
    graph = {}
    fixed_usage = {}
    for name, op, lhs, rhs in assembled:
        assert name not in available and op in {'+', '-', '*'}
        dependencies = []
        for item in (lhs, rhs):
            if isinstance(item, str):
                assert item in available
                dependencies.append(item)
            elif isinstance(item, dict):
                assert set(item) == {'fixed'} and item['fixed'] not in fixed_usage
                fixed_usage[item['fixed']] = op
            else:
                assert type(item) is int
        graph[name] = dependencies
        available.add(name)
    live = set()
    pending = [old['output']]
    while pending:
        next_name = pending.pop()
        if next_name not in live:
            live.add(next_name)
            pending += graph.get(next_name, [])
    assert available <= live
    assert len(fixed_usage) == 6+15*r
    assert sorted(fixed_usage) == old['static_checks']['named_fixed_roles']
    assert {key: op for key, op in fixed_usage.items() if op != '*'} == {'gamma': '+'}
    for field in ['ports', 'comparisons', 'centered_input_forms', 'lanes_in_order',
                  'selected_center_ports', 'parent_suffix_bindings', 'quotient_pair_ports']:
        assert all(value in available for _, value in text_leaves(old[field]))

    child = {key: value for key, value in old.items()
             if key not in {'grouped_right_splice','grouped_right_support_products','joint_right_native_products'}}
    child.update(source=assembled, stages=new_stages,
                 polynomial_ledger=ledger(assembled), certificate_ledger=ledger(assembled[:-68]),
                 certificate_prefix_rows=len(assembled)-68,
                 shared_left_right_support_products=len(support), joint_pack_native_products=len(support)+1)
    # Every untouched field is the identical inherited object; all changed fields are listed below.
    child['static_checks'] = {'topology':True, 'all_computed_live':True,
                              'all_supplied_live':True, 'named_fixed_roles':sorted(fixed_usage)}
    changed = sorted(key for key in set(old) | set(child) if old.get(key) != child.get(key))
    child['grouped_left_splice'] = {
        'local_proof_sha256':LOCAL_PIN, 'parent_receipt_sha256':PARENT_PIN,
        'historical_parent_splice':'grouped_right_splice belongs to the immutable parent receipt; not an active current binding',
        'removed_rows':old_cone, 'inserted_rows':new_cone, 'moved_literal_rows':support,
        'unmoved_literal_row_names':unmoved_literal,
        'old_cut_ledger':ledger(old_cone), 'new_cut_ledger':ledger(new_cone),
        'preserved_exit':'left_six_high_join_a', 'external_consumer_rows':external,
        'preserved_active_mentions':mentions, 'rewritten_outside_rows':[],
        'source_sha256_before':digest(rows), 'source_sha256_after':digest(assembled),
        'support_insertion_before':'left_high_tail_shift',
        'new_cone_insertion_at_old_exit':'left_six_high_join_a',
        'changed_top_level_fields':sorted(changed + ['grouped_left_splice']),
        'support_cost_scope':'All2/3/4 shared support products moved from right to left stage, still charged once; final native link remains1M.',
        'actual_scope':'Complete saved uniform r1/2/4 only; collected Gamma relocation is the separate handwritten general grammar.'}
    children.append(child)

result = {
    'status':'FROZEN first original metadata-only composition; never replay this emitter',
    'emitter_sha256':sha(Path(__file__).read_bytes()),
    'inputs':[{'path':str(PARENT), 'sha256':PARENT_PIN, 'bytes':len(parent_bytes)}],
    'local_proof_sha256':LOCAL_PIN,
    'generic_ledger':{
        'domain':'r>=1,m=8+2r; inherited geometric costs and A,B,D18,E24,eta indicators',
        'uniform_certificate':'(196+27r+gM-A-B-D18-E24)M+(463+40r+gA-B)A',
        'uniform_polynomial':'(219+27r+gM-A-B-D18-E24)M+(508+40r+gA-B)A',
        'uniform_operations':'727+67r+gM+gA-A-2B-D18-E24',
        'collected_certificate':'(199+27r+gM-A-B-D18-E24-eta)M+(467+39r+gA-B-eta)A',
        'collected_polynomial':'(222+27r+gM-A-B-D18-E24-eta)M+(512+39r+gA-B-eta)A',
        'collected_operations':'734+66r+gM+gA-A-2B-D18-E24-2eta',
        'saving':'rM and0A relative to grouped-right parent; supports are moved, not unpaid',
        'fixture_adjustment':'Subtract inheritedf(1)=3,f(2)=2,f(4)=1 from genericM; actual totals798/862/1003',
        'collected_restoration':'Retain Gamma producer; replace its one restoration add by the same add inside theP24 factor.',
        'scope':'Handwritten general grammar; only supplied uniformr1/2/4 graphs emitted, no collected or missing alias fixture invented.',
        'witnesses':'96+6r','equations':23,'fixed_roles':'6+15r; gamma is the unique addition role'},
    'fixed_data_recipe':parent['fixed_data_recipe'], 'r0_fallback':parent['r0_fallback'],
    'examples':children,
    'execution_scope':'Original record construction, equality, count, topology, liveness and metadata checks only; no instruction/coeff evaluation, scientific execution, symbolic values, degrees, helper imports/replay or build.'}
assert sum(len(child['source']) for child in children) == 2663
DESTINATION.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
print('PASS: 2663 inert complete records; r1/r2/r4 totals798/862/1003; no source arithmetic evaluated.')
