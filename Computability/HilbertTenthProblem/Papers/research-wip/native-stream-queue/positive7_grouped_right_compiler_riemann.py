"""Fresh record-only grouped-right composer. Do not run before root preflight.

One lifetime metadata-only run. Never interpret arithmetic instruction values.
"""
from pathlib import Path
from collections import Counter
import copy
import hashlib
import json

REPO = Path('/home/codex/.codex/worktrees/2a71/Proofs')
INPUT = REPO / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/positive7_common_center_compiler_root.json'
INPUT_SHA = 'ff634059250ac399883ae3311a81354204a84be82b6ae973983e2e9e95b7d6db'
DEST = Path('/tmp/positive7_grouped_right_compiler_riemann.json')
THEOREM_SHA = '2f3832c6537e82ee4f2c016b2cc05729a199125c68e1e82c9b83e149f990a31a'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def counts(rows):
    labels = Counter(row[1] for row in rows)
    assert not set(labels) - {'*', '+', '-'}
    return {'M': labels['*'], 'A': labels['+'] + labels['-'], 'operations': len(rows)}


def records_sha(rows):
    return sha(json.dumps(rows, separators=(',', ':')).encode())


def source_blocks(graph):
    answer = {}; position = 0
    for key, ledger in graph['stages'].items():
        stop = position + ledger['operations']
        answer[key] = graph['source'][position:stop]
        assert counts(answer[key]) == ledger
        position = stop
    assert position == len(graph['source'])
    assert len({q[0] for q in graph['source']}) == position
    return answer


def design(parent):
    r, m = parent['r'], parent['m']
    assert m == 8 + 2*r and r >= 1 and parent['ell'] == 62 + 6*r
    bits = format(m, 'b')
    flag_c = int(bits.startswith('10011'))
    d18 = int(len(bits) >= 5 and bits.startswith('1001'))
    e24 = int(len(bits) >= 5 and bits.startswith('1100'))
    assert flag_c <= d18
    P = parent['ports']['P']; Pm = parent['ports']['selector_power']
    P12 = parent['ports']['left_support_P12']
    declared = {row[0]: row for row in parent['source']}
    order = {row[0]: n for n, row in enumerate(parent['source'])}
    old = []
    for width in (2, 6, 7):
        old.append([f'pack_C{width}', '*', 'cell_mask', f'pack_R{width}'])
    acc = 'right_tail_product'
    for i in reversed(range(m)):
        width = 6 if i < 4 else 7 if i < 8 else 2
        upper = f'right_block_shift_{i}'; lower = f'right_block_lower_{i}'
        power = 'scale_square_0' if width == 2 else f'pack_P{width}'
        old.extend([[upper, '*', acc, power],
                    [lower, '*', f'pack_C{width}', f'selector_{i}'],
                    [f'right_block_join_{i}', '+', upper, lower]])
        acc = f'right_block_join_{i}'
    p19 = 'geom_P19' if flag_c else 'native_shared_P19'
    if not flag_c:
        old.append([p19, '*', P12, 'pack_P7'])
    old.extend([['native_shared_m_plus_19', '*', Pm, p19],
                ['native_shared_double', '*', 'native_shared_m_plus_19', 'native_shared_m_plus_19'],
                ['native_shared_scale', '*', Pm, 'native_shared_double']])
    for row in old:
        assert declared[row[0]] == row, ('parent cut mismatch', row[0])
    removed = {q[0] for q in old}
    assert len(removed) == len(old)
    assert counts(old) == {'M': 23 + 4*r - flag_c, 'A': 8 + 2*r, 'operations': 31 + 6*r - flag_c}
    assert parent['native_scale_products'] == 4 - flag_c
    assert declared['right_selector_shift'] == ['right_selector_shift', '*', 'right_block_join_0', Pm]
    assert declared['right_tail_sum'] == ['right_tail_sum', '+', parent['ports']['J'], P]
    assert declared['right_tail_product'] == ['right_tail_product', '*', 'height_mask', 'right_tail_sum']
    assert declared['pell_q'] == ['pell_q', '*', 16, 'native_shared_scale']
    outside_uses = []
    for row in parent['source']:
        if row[0] not in removed:
            for slot, operand in enumerate(row[2:], 2):
                if isinstance(operand, str) and operand in removed:
                    outside_uses.append([operand, row[0], slot])
    assert sorted(outside_uses) == [['native_shared_scale', 'pell_q', 3], ['right_block_join_0', 'right_selector_shift', 2]]

    prelude = []
    p28 = 'left_support_P28' if 'left_support_P28' in declared else 'geom_P28'
    p14 = 'left_support_P14' if 'left_support_P14' in declared else 'geom_P14'
    assert p28 in declared and order[p28] < order['right_tail_sum']
    p24 = 'geom_P24' if e24 else 'group_right_P24'
    p18 = 'geom_P18' if d18 else 'group_right_P18'
    for flag, name in ((e24, p24), (d18, p18)):
        if flag:
            assert name in declared and order[name] < order['right_tail_sum']
    if not e24: prelude.append([p24, '*', P12, P12])
    fixture = {1: 'H=P28^2; native factor=P12',
               2: 'Y=P28*P2; H=Y^2; native factor=P14',
               4: 'native factor=P18'}.get(r)
    if r == 1:
        prelude.append(['group_right_tail_power', '*', p28, p28])
        native_factor = P12
    elif r == 2:
        assert p14 in declared and order[p14] < order['right_tail_sum']
        prelude.extend([['group_right_m18', '*', p28, 'scale_square_0'],
                        ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']])
        native_factor = p14
    else:
        if not d18: prelude.append([p18, '*', P12, 'pack_P6'])
        prelude.extend([['group_right_m18', '*', Pm, p18],
                        ['group_right_tail_power', '*', 'group_right_m18', 'group_right_m18']])
        native_factor = p18 if r == 4 else 'group_right_native_factor'
    support_count = {1:2, 2:3, 4:4}.get(r, 4-d18-e24)
    assert counts(prelude) == {'M': support_count, 'A': 0, 'operations': support_count}
    support = copy.deepcopy(prelude)
    q_exits = {}
    for tag, start, end, radix in [('q6', 0, 4, 'pack_P6'), ('q7', 4, 8, 'pack_P7'), ('q2', 8, m, 'scale_square_0')]:
        value = f'selector_{end-1}'
        for i in range(end-2, start-1, -1):
            product = f'group_right_{tag}_mul_{i}'
            result = f'group_right_{tag}_add_{i}'
            prelude.extend([[product, '*', value, radix], [result, '+', product, f'selector_{i}']])
            value = result
        q_exits[tag] = value
    high = [
        ['group_right_coeff2', '*', 'pack_R2', q_exits['q2']],
        ['group_right_coeff7', '*', 'pack_R7', q_exits['q7']],
        ['group_right_coeff6', '*', 'pack_R6', q_exits['q6']],
        ['group_right_shift2', '*', p28, 'group_right_coeff2'],
        ['group_right_middle', '+', 'group_right_shift2', 'group_right_coeff7'],
        ['group_right_shift7', '*', p24, 'group_right_middle'],
        ['group_right_lower', '+', 'group_right_shift7', 'group_right_coeff6'],
        ['group_right_selected', '*', 'cell_mask', 'group_right_lower'],
        ['group_right_upper', '*', 'group_right_tail_power', 'right_tail_product'],
        ['right_block_join_0', '+', 'group_right_selected', 'group_right_upper']]
    native = []
    if fixture is None:
        native.append(['group_right_native_factor', '*', Pm, 'scale_square_0'])
    native.append(['native_shared_scale', '*', 'group_right_tail_power', native_factor])
    extra_fixture_saving = {1:3, 2:2, 4:1}.get(r, 0)
    inserted = prelude + high + native
    assert counts(high) == {'M': 7, 'A': 3, 'operations': 10}
    assert counts(inserted) == {'M': 18+2*r-d18-e24-extra_fixture_saving, 'A': 8+2*r,
                               'operations': 26+4*r-d18-e24-extra_fixture_saving}
    reused = {q[0] for q in inserted} & set(declared)
    assert reused == {'right_block_join_0', 'native_shared_scale'}
    assert len({q[0] for q in inserted}) == len(inserted)
    return dict(old=old, removed=removed, prelude=prelude, high=high, native=native, inserted=inserted,
                support=support, exits=q_exits, outside_uses=outside_uses, C=flag_c, D18=d18, E24=e24,
                fixture=fixture, fixture_saving=extra_fixture_saving, support_count=support_count,
                native_count=len(native), native_factor=native_factor)


def audit_graph(graph):
    supplied = graph['ordinary_parameters'] + graph['positive_auxiliaries']
    assert len(supplied) == len(set(supplied))
    known = set(supplied); dependencies = {}; role_ops = {}; multiplicities = Counter()
    for name, op, a, b in graph['source']:
        assert name not in known and op in ('+', '-', '*')
        dependencies[name] = []
        for operand in (a, b):
            if isinstance(operand, str):
                assert operand in known, (name, operand)
                dependencies[name].append(operand)
            elif type(operand) is dict:
                assert set(operand) == {'fixed'}
                role = operand['fixed']; multiplicities[role] += 1; role_ops[role] = op
            else:
                assert type(operand) is int
        known.add(name)
    reached = set(); todo = [graph['output']]
    while todo:
        node = todo.pop()
        if node not in reached:
            reached.add(node); todo += dependencies.get(node, [])
    assert known <= reached
    assert set(multiplicities.values()) == {1} and len(multiplicities) == 6+15*graph['r']
    assert {k:v for k,v in role_ops.items() if v != '*'} == {'gamma': '+'}
    assert sorted(multiplicities) == graph['static_checks']['named_fixed_roles']
    def bind(value):
        if isinstance(value, str): assert value in known, value
        elif isinstance(value, list):
            for item in value: bind(item)
        elif isinstance(value, dict):
            for item in value.values(): bind(item)
        else: assert type(value) is int
    for key in ['ports', 'centered_input_forms', 'lanes_in_order', 'selected_center_ports', 'comparisons', 'quotient_pair_ports']:
        bind(graph[key])
    assert len(graph['positive_auxiliaries']) == 96+6*graph['r']
    assert len(graph['comparisons']) == 23
    return dict(topology=True, all_computed_live=True, all_supplied_live=True, named_fixed_roles=sorted(multiplicities))


def compose(parent):
    plan = design(parent); blocks = source_blocks(parent)
    rename = {'shared_pack_powers_and_coefficients': 'shared_pack_powers_and_repunits',
              'factored_pack_joins': 'grouped_right_pack_and_joins',
              'shared_native_scale': 'native_scale_from_right_tail_power'}
    source = []; stage_rows = {}; literal = []; inserted_seen = []
    for stage, rows in blocks.items():
        built = []
        if stage == 'shared_native_scale':
            assert {q[0] for q in rows} == {q[0] for q in plan['old'] if q[0].startswith('native_shared_')}
            built.extend(plan['native']); inserted_seen.extend(plan['native'])
        else:
            for row in rows:
                if row[0] == 'right_tail_sum':
                    built.extend(plan['prelude']); inserted_seen.extend(plan['prelude'])
                if row[0] == 'right_selector_shift':
                    built.extend(plan['high']); inserted_seen.extend(plan['high'])
                if row[0] not in plan['removed']:
                    built.append(row); literal.append(row)
        stage_rows[rename.get(stage, stage)] = built
        source.extend(built)
    assert inserted_seen == plan['inserted']
    assert len(source) == len(literal) + len(inserted_seen)
    assert len(parent['source']) == len(literal) + len(plan['old'])
    assert source[-68:] == parent['source'][-68:]
    assert stage_rows['complete_native64'] == blocks['complete_native64']
    assert counts(stage_rows['shared_pack_powers_and_repunits']) == {'M': 5, 'A': 4, 'operations': 9}
    r = parent['r']; d = plan['D18']; e = plan['E24']
    support_saving = (4-d-e) - plan['support_count']
    assert counts(stage_rows['grouped_right_pack_and_joins']) == {'M': 21+2*r-d-e-support_saving,
                 'A': 12+2*r, 'operations': 33+4*r-d-e-support_saving}
    assert counts(stage_rows['native_scale_from_right_tail_power']) == {'M': plan['native_count'], 'A': 0,
                                                                      'operations': plan['native_count']}
    child = copy.deepcopy(parent)
    del child['common_center_splice']
    child.update(source=source, stages={key:counts(rows) for key,rows in stage_rows.items()},
                 native_scale_products=plan['native_count'], grouped_right_support_products=plan['support_count'],
                 joint_right_native_products=plan['support_count']+plan['native_count'], certificate_prefix_rows=len(source)-68,
                 certificate_ledger=counts(source[:-68]), polynomial_ledger=counts(source))
    child['static_checks'] = audit_graph(child)
    assert child['static_checks'] == parent['static_checks']
    expected = {1:(248,551), 2:(275,589), 4:(336,671)}
    assert (child['polynomial_ledger']['M'],child['polynomial_ledger']['A']) == expected[r]
    parent_count = parent['polynomial_ledger']; current_count = child['polynomial_ledger']
    assert parent_count['M'] - current_count['M'] == 2*r+5-plan['C']+d+e+plan['fixture_saving']
    assert parent_count['A'] == current_count['A']
    child['grouped_right_splice'] = dict(
        theorem_sha256=THEOREM_SHA, flags={key:plan[key] for key in ['C','D18','E24']},
        deleted_rows=plan['old'], inserted_rows=inserted_seen, literal_retained_row_names=[q[0] for q in literal],
        old_cut_ledger=counts(plan['old']), new_cut_ledger=counts(inserted_seen),
        preserved_exit_names=['right_block_join_0','native_shared_scale'], external_consumers=plan['outside_uses'],
        rewritten_external_rows=[], selector_horner_exits=plan['exits'], shared_support_rows=plan['support'],
        source_sha256_before=records_sha(parent['source']), source_sha256_after=records_sha(source),
        stage_renames=rename, removed_parent_receipt='common_center_splice',
        parent_receipt_provenance='The immutable input packet retains the common-center receipt; it is not active child register metadata.',
        fixture_specialization=plan['fixture'], extra_fixture_saving_M=plan['fixture_saving'],
        native_factor_binding=plan['native_factor'],
        native_cost_scope='Native links are paid separately from shared support. Generic costs2 and4-D18-E24; saved fixture costs1 and2/3/4, joint3/4/5.',
        actual_scope='Existing r1/2/4 only; all D18=E24=C=0. No collected or general-prefix source example is invented.')
    permitted = {'source','stages','native_scale_products','grouped_right_support_products','joint_right_native_products',
                 'certificate_prefix_rows','certificate_ledger','polynomial_ledger','grouped_right_splice','common_center_splice'}
    all_keys = set(child) | set(parent)
    changed = sorted(k for k in all_keys if child.get(k) != parent.get(k))
    assert set(changed) <= permitted
    child['grouped_right_splice']['changed_top_level_fields'] = changed
    child['grouped_right_splice']['all_other_fields_literal'] = True
    return child


assert not DEST.exists(), 'Do not replay: output must not already exist'
input_bytes = INPUT.read_bytes()
assert sha(input_bytes) == INPUT_SHA
received = json.loads(input_bytes)
assert [g['r'] for g in received['examples']] == [1,2,4]
completed = [compose(g) for g in received['examples']]
assert sum(len(g['source']) for g in completed) == 2670
receipt = dict(
    status='FROZEN first original record-only composition; never replay this emitter',
    emitter_sha256=sha(Path(__file__).read_bytes()),
    inputs=[dict(path=str(INPUT),sha256=INPUT_SHA,bytes=len(input_bytes))],
    local_proof_sha256=THEOREM_SHA,
    generic_ledger=dict(
        domain='r>=1; m=8+2r; inherited A/B/C/eta; D18 is prefix1001 with >=5 bits; E24 is prefix1100 with >=5 bits',
        uniform_certificate='(196+28r+gM-A-B-D18-E24)M+(463+40r+gA-B)A',
        uniform_polynomial='(219+28r+gM-A-B-D18-E24)M+(508+40r+gA-B)A',
        uniform_operations='727+68r+gM+gA-A-2B-D18-E24',
        collected_certificate='(199+28r+gM-A-B-D18-E24-eta)M+(467+39r+gA-B-eta)A',
        collected_polynomial='(222+28r+gM-A-B-D18-E24-eta)M+(512+39r+gA-B-eta)A',
        collected_operations='734+67r+gM+gA-A-2B-D18-E24-2eta',
        saving='(2r+5-C+D18+E24)M and0A relative to common-center parent; at least2r+5M',
        old_cut='(23+4r-C)M+(8+2r)A', new_cut='(18+2r-D18-E24)M+(8+2r)A',
        support_products='4-D18-E24',native_scale_products=2,joint_right_native_products='6-D18-E24',
        fixture_specializations='r1/r2/r4 additionally save3/2/1M respectively; actual native links1M, shared support2/3/4M; counts799/864/1007',
        retained_unspecialized_fixture_counts=[802,866,1008],
        witnesses='96+6r',equations=23,fixed_roles='6+15r',geometric_cost=received['generic_ledger']['geometric_cost'],
        scope='General formulas are handwritten grammar conclusions. Only the three supplied uniform examples are emitted; no r>=8 example is claimed.'),
    fixed_data_recipe=copy.deepcopy(received['fixed_data_recipe']),r0_fallback=copy.deepcopy(received['r0_fallback']),examples=completed,
    execution_scope='Fresh original metadata-only record construction and identity/topology/consumer/count/liveness checks. No arithmetic instruction evaluation, coefficient specialization, symbolic evaluation, degree propagation, scientific sampling, helper import/replay, or build.')
DEST.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
print('PASS one lifetime metadata composition:2670 records;799/864/1007; freeze emitter and receipt')
