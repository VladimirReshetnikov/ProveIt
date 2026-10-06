"""Independent original static audit. PRE-RUN DRAFT; root must read first.

Only JSON records, bytes and graph names are inspected. No operator field is
interpreted, no polynomial is evaluated, and no supplied module is imported.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

PARENT = Path('/tmp/positive7_common_center_compiler_root.json')
CHILD = Path('/tmp/positive7_grouped_right_compiler_riemann.json')
COMPOSER = Path('/tmp/positive7_grouped_right_compiler_riemann.py')
PRIMARY = Path('/tmp/positive7_grouped_right_compiler_riemann.md')
REPORT = Path('/tmp/review_positive7_grouped_right_static_pascal.json')
EXPECTED_PARENT = 'ff634059250ac399883ae3311a81354204a84be82b6ae973983e2e9e95b7d6db'
EXPECTED_CHILD = '4a21f5cfe0e33ac847ed8eaed19355b5047ea8dc84c822c4170e2f2c3947fa8c'
EXPECTED_COMPOSER = '4ce81f4690fed2d6da8564c0fb804f200c74d4032ca36b8e1153c7877091d9a9'
EXPECTED_LOCAL = '2f3832c6537e82ee4f2c016b2cc05729a199125c68e1e82c9b83e149f990a31a'
EXPECTED_PRIMARY = '71a9052087df453825324d9a19e9f5bc3f7ba645f9ade283607bc413b55e2cc6'


def digest(b):
    return hashlib.sha256(b).hexdigest()


def compact(x):
    return json.dumps(x, separators=(',', ':')).encode()


def load_bound(path, wanted):
    raw = path.read_bytes()
    assert digest(raw) == wanted, ('byte identity', str(path))
    return json.loads(raw), {'path': str(path), 'sha256': wanted, 'bytes': len(raw)}


def census(rows):
    operations = Counter(item[1] for item in rows)
    assert set(operations) <= {'+', '-', '*'}
    return {'M': operations['*'], 'A': operations['+'] + operations['-'], 'operations': len(rows)}


def stages_of(g):
    cursor = 0; blocks = {}
    for stage, summary in g['stages'].items():
        stop = cursor + summary['operations']
        block = g['source'][cursor:stop]
        assert census(block) == summary, ('stage census', stage)
        blocks[stage] = block
        cursor = stop
    assert cursor == len(g['source'])
    return blocks


def graph_scan(g):
    given = g['ordinary_parameters'] + g['positive_auxiliaries']
    assert len(given) == len(set(given))
    available = set(given); predecessors = {}; roles = []
    for row in g['source']:
        assert type(row) is list and len(row) == 4
        label, op, *operands = row
        assert type(label) is str and label not in available
        assert op in ('*', '+', '-')
        inputs = []
        for value in operands:
            if type(value) is str:
                assert value in available, ('forward or missing reference', label, value)
                inputs.append(value)
            elif type(value) is dict:
                assert list(value) == ['fixed'] and type(value['fixed']) is str
                roles.append((value['fixed'], op, label))
            else:
                assert type(value) is int
        predecessors[label] = inputs
        available.add(label)
    assert g['output'] in predecessors
    live = set(); pending = [g['output']]
    while pending:
        v = pending.pop()
        if v in live:
            continue
        live.add(v); pending.extend(predecessors.get(v, ()))
    assert live == available, ('dead names', sorted(available-live))
    names = [entry[0] for entry in roles]
    assert len(names) == 6 + 15*g['r'] and len(names) == len(set(names))
    assert [(name, op) for name, op, _ in roles if op != '*'] == [('gamma', '+')]
    assert sorted(names) == g['static_checks']['named_fixed_roles']
    assert g['static_checks'] == {'topology': True, 'all_computed_live': True,
                                'all_supplied_live': True, 'named_fixed_roles': sorted(names)}
    def reference_tree(v):
        if type(v) is str:
            assert v in available, ('metadata name', v)
        elif type(v) is list:
            for item in v: reference_tree(item)
        elif type(v) is dict:
            for item in v.values(): reference_tree(item)
        else:
            assert type(v) is int
    for field in ('ports', 'centered_input_forms', 'lanes_in_order',
                  'selected_center_ports', 'comparisons', 'quotient_pair_ports'):
        reference_tree(g[field])
    assert len(g['comparisons']) == g['equations'] == 23
    assert len(g['positive_auxiliaries']) == g['witnesses'] == 96 + 6*g['r']
    return roles


def expected_fixture(g):
    """Hand-derived saved-fixture grammar; no claim of testing absent r values."""
    r = g['r']; m = g['m']; assert r in (1, 2, 4) and m == 8 + 2*r
    Pm = {1: 'geom_P10', 2: 'geom_P12', 4: 'geom_P16'}[r]
    P12 = 'geom_P12' if r == 2 else 'left_support_P12'
    assert g['ports']['selector_power'] == Pm
    assert g['ports']['left_support_P12'] == P12
    old = [[f'pack_C{w}', '*', 'cell_mask', f'pack_R{w}'] for w in (2, 6, 7)]
    for i in range(m-1, -1, -1):
        preceding = 'right_tail_product' if i == m-1 else f'right_block_join_{i+1}'
        w = 6 if i <= 3 else 7 if i <= 7 else 2
        old += [[f'right_block_shift_{i}', '*', preceding,
                 'scale_square_0' if w == 2 else f'pack_P{w}'],
                [f'right_block_lower_{i}', '*', f'pack_C{w}', f'selector_{i}'],
                [f'right_block_join_{i}', '+', f'right_block_shift_{i}', f'right_block_lower_{i}']]
    old += [['native_shared_P19', '*', P12, 'pack_P7'],
            ['native_shared_m_plus_19', '*', Pm, 'native_shared_P19'],
            ['native_shared_double', '*', 'native_shared_m_plus_19', 'native_shared_m_plus_19'],
            ['native_shared_scale', '*', Pm, 'native_shared_double']]
    support = [['group_right_P24', '*', P12, P12]]
    if r == 1:
        support += [['group_right_tail_power', '*', 'left_support_P28', 'left_support_P28']]
        factor = P12
    elif r == 2:
        support += [['group_right_m18', '*', 'left_support_P28', 'scale_square_0'],
                    ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']]
        factor = 'left_support_P14'
    else:
        support += [['group_right_P18', '*', P12, 'pack_P6'],
                    ['group_right_m18', '*', Pm, 'group_right_P18'],
                    ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']]
        factor = 'group_right_P18'
    pre = list(support); exits = {}
    for tag, indices, power in [('q6', [3,2,1,0], 'pack_P6'),
                                ('q7', [7,6,5,4], 'pack_P7'),
                                ('q2', list(range(m-1,7,-1)), 'scale_square_0')]:
        value = f'selector_{indices[0]}'
        for i in indices[1:]:
            mul = f'group_right_{tag}_mul_{i}'; add = f'group_right_{tag}_add_{i}'
            pre += [[mul, '*', value, power], [add, '+', mul, f'selector_{i}']]
            value = add
        exits[tag] = value
    high = [['group_right_coeff2', '*', 'pack_R2', exits['q2']],
            ['group_right_coeff7', '*', 'pack_R7', exits['q7']],
            ['group_right_coeff6', '*', 'pack_R6', exits['q6']],
            ['group_right_shift2', '*', 'left_support_P28', 'group_right_coeff2'],
            ['group_right_middle', '+', 'group_right_shift2', 'group_right_coeff7'],
            ['group_right_shift7', '*', 'group_right_P24', 'group_right_middle'],
            ['group_right_lower', '+', 'group_right_shift7', 'group_right_coeff6'],
            ['group_right_selected', '*', 'cell_mask', 'group_right_lower'],
            ['group_right_upper', '*', 'group_right_tail_power', 'right_tail_product'],
            ['right_block_join_0', '+', 'group_right_selected', 'group_right_upper']]
    native = [['native_shared_scale', '*', 'group_right_tail_power', factor]]
    return old, pre, high, native, support, exits, factor


def compare_one(before, after):
    r = before['r']; old, pre, high, native, support, exits, factor = expected_fixture(before)
    old_names = {row[0] for row in old}; old_def = {row[0]: row for row in before['source']}
    assert all(old_def[row[0]] == row for row in old)
    external = sorted((v, row[0], j) for row in before['source'] if row[0] not in old_names
                      for j, v in enumerate(row[2:], 2) if type(v) is str and v in old_names)
    assert external == [('native_shared_scale','pell_q',3), ('right_block_join_0','right_selector_shift',2)]
    block_map = stages_of(before); expected = []; renamed = {}; survivors = []
    stage_names = {'shared_pack_powers_and_coefficients':'shared_pack_powers_and_repunits',
                   'factored_pack_joins':'grouped_right_pack_and_joins',
                   'shared_native_scale':'native_scale_from_right_tail_power'}
    for stage, rows in block_map.items():
        result = []
        for row in rows:
            if row[0] == 'right_tail_sum': result += pre
            if row[0] == 'right_selector_shift': result += high
            if row[0] == 'native_shared_P19': result += native
            if row[0] not in old_names:
                result.append(row); survivors.append(row)
        renamed[stage_names.get(stage,stage)] = result
        expected += result
    assert after['source'] == expected, ('complete source mismatch',r)
    assert stages_of(after) == renamed
    assert after['source'][-68:] == before['source'][-68:]
    assert renamed['complete_native64'] == block_map['complete_native64']
    assert after['stages'] == {k:census(v) for k,v in renamed.items()}
    assert after['certificate_prefix_rows'] == len(expected)-68
    assert after['certificate_ledger'] == census(expected[:-68])
    assert after['polynomial_ledger'] == census(expected)
    assert (len(expected),after['polynomial_ledger']['M'],after['polynomial_ledger']['A']) == {1:(799,248,551),2:(864,275,589),4:(1007,336,671)}[r]
    assert after['native_scale_products'] == 1
    assert after['grouped_right_support_products'] == {1:2,2:3,4:4}[r]
    assert after['joint_right_native_products'] == {1:3,2:4,4:5}[r]
    allowed = {'source','stages','native_scale_products','grouped_right_support_products',
               'joint_right_native_products','certificate_prefix_rows','certificate_ledger',
               'polynomial_ledger','grouped_right_splice','common_center_splice'}
    changed = {key for key in set(before)|set(after) if before.get(key)!=after.get(key)}
    assert changed == allowed
    assert 'common_center_splice' not in after
    assert graph_scan(before) == graph_scan(after)
    splice = after['grouped_right_splice']; inserted = pre+high+native
    assert splice['theorem_sha256'] == EXPECTED_LOCAL
    assert splice['flags'] == {'C':0,'D18':0,'E24':0}
    assert splice['deleted_rows'] == old and splice['inserted_rows'] == inserted
    assert splice['literal_retained_row_names'] == [row[0] for row in survivors]
    assert splice['old_cut_ledger'] == census(old) and splice['new_cut_ledger'] == census(inserted)
    assert splice['preserved_exit_names'] == ['right_block_join_0','native_shared_scale']
    assert sorted(tuple(item) for item in splice['external_consumers']) == external
    assert splice['rewritten_external_rows'] == []
    assert splice['selector_horner_exits'] == exits and splice['shared_support_rows'] == support
    assert splice['source_sha256_before'] == digest(compact(before['source']))
    assert splice['source_sha256_after'] == digest(compact(after['source']))
    assert splice['stage_renames'] == stage_names and splice['native_factor_binding'] == factor
    assert splice['extra_fixture_saving_M'] == {1:3,2:2,4:1}[r]
    assert splice['changed_top_level_fields'] == sorted(changed)
    assert splice['all_other_fields_literal'] is True
    return {'r':r,'whole_source_rows_checked':len(expected),'literal_rows':len(survivors),
            'removed_rows':len(old),'inserted_rows':len(inserted),'full':census(expected),
            'certificate':census(expected[:-68]),'all_rows_identity_and_topology':True,
            'native64_and_final68_literal':True,'metadata_and_roles_pass':True}


assert not REPORT.exists(), 'Single-use independent audit receipt already exists'
parent, ppin = load_bound(PARENT, EXPECTED_PARENT)
child, cpin = load_bound(CHILD, EXPECTED_CHILD)
composer_bytes = COMPOSER.read_bytes()
assert digest(composer_bytes) == EXPECTED_COMPOSER
primary_bytes = PRIMARY.read_bytes()
assert digest(primary_bytes) == EXPECTED_PRIMARY
assert child['emitter_sha256'] == EXPECTED_COMPOSER and child['local_proof_sha256'] == EXPECTED_LOCAL
assert len(child['inputs']) == 1 and child['inputs'][0]['sha256'] == EXPECTED_PARENT
assert child['inputs'][0]['bytes'] == ppin['bytes']
assert child['fixed_data_recipe'] == parent['fixed_data_recipe']
assert child['r0_fallback'] == parent['r0_fallback']
assert [x['r'] for x in parent['examples']] == [x['r'] for x in child['examples']] == [1,2,4]
results = [compare_one(a,b) for a,b in zip(parent['examples'],child['examples'])]
assert sum(r['whole_source_rows_checked'] for r in results) == 2670
assert sum(r['literal_rows'] for r in results) == 2570
assert sum(r['inserted_rows'] for r in results) == 100
assert child['generic_ledger']['geometric_cost'] == parent['generic_ledger']['geometric_cost']
assert child['generic_ledger']['uniform_polynomial'] == '(219+28r+gM-A-B-D18-E24)M+(508+40r+gA-B)A'
assert child['generic_ledger']['collected_polynomial'] == '(222+28r+gM-A-B-D18-E24-eta)M+(512+39r+gA-B-eta)A'
assert child['generic_ledger']['retained_unspecialized_fixture_counts'] == [802,866,1008]
for key, expected_text in {
    'uniform_certificate':'(196+28r+gM-A-B-D18-E24)M+(463+40r+gA-B)A',
    'collected_certificate':'(199+28r+gM-A-B-D18-E24-eta)M+(467+39r+gA-B-eta)A',
    'uniform_operations':'727+68r+gM+gA-A-2B-D18-E24',
    'collected_operations':'734+67r+gM+gA-A-2B-D18-E24-2eta',
    'old_cut':'(23+4r-C)M+(8+2r)A', 'new_cut':'(18+2r-D18-E24)M+(8+2r)A',
    'support_products':'4-D18-E24','joint_right_native_products':'6-D18-E24',
    'witnesses':'96+6r','fixed_roles':'6+15r'}.items():
    assert child['generic_ledger'][key] == expected_text
assert child['generic_ledger']['native_scale_products'] == 2
assert child['generic_ledger']['equations'] == 23
receipt = {'status':'PASS; independent original one-run static audit frozen',
           'checker_sha256':digest(Path(__file__).read_bytes()), 'parent':ppin,'child':cpin,
           'composer_sha256':EXPECTED_COMPOSER,'primary_sha256':EXPECTED_PRIMARY,'examples':results,
           'scope':'All complete saved rows compared with an independent hand-derived literal splice; static counts, bindings, topology, liveness and metadata only. No arithmetic instruction evaluation, coefficient specialization, symbolic execution, degree calculation, scientific code or supplied-helper replay.',
           'unsaved_scope':'All-r/prefix/collected grammar is handwritten proof, not new saved-array evidence; r0 inherited byte-identically.',
           'retained_boundaries':'Gamma is an addition role; generic802/866/1008 remains valid and is improved only by the three proved fixed-m aliases.'}
REPORT.write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS2670 complete rows;2570 literal+100 new;799/864/1007; no arithmetic evaluation; freeze checker and receipt')
