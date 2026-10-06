"""Original inert-record common-center composer. Sole run, then freeze forever.

No instruction evaluation, coefficient specialization or degree propagation.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter
import hashlib
import json

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT = BASE / 'positive7_power_alias_compiler_root.json'
DEST = Path('/tmp/positive7_common_center_compiler_root.json')
assert not DEST.exists(), 'No replay of an already emitted source'
raw = PARENT.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'e2985ae7fa1754c347261bca096c4d360f263bcbabf58481f7a0e1d305558b2a'
packet = json.loads(raw)


def row_counts(records):
    tally = Counter(record[1] for record in records)
    assert set(tally) <= {'+', '-', '*'}
    return {'M': tally['*'], 'A': tally['+'] + tally['-'], 'operations': len(records)}


def record_digest(records):
    return hashlib.sha256(json.dumps(records, separators=(',', ':')).encode()).hexdigest()


def semantic_rebinding(value, descriptions):
    if type(value) is str:
        return deepcopy(descriptions.get(value, value))
    if type(value) is list:
        return [semantic_rebinding(item, descriptions) for item in value]
    if type(value) is dict:
        return {key: semantic_rebinding(item, descriptions) for key, item in value.items()}
    return value


examples = []
for prior in packet['examples']:
    r = prior['r']; m = prior['m']
    assert r >= 1 and m == 8 + 2*r
    route = 'uniform' if r <= 7 else 'collected'
    eta = int(bin(m)[2:].startswith('100'))
    definitions = {record[0]: record for record in prior['source']}
    descriptions = {}
    consumer_changes = {}
    for j in range(r):
        first = f'centered_form_{j}_1'; second = f'centered_form_{j}_2'
        u = f'decoded_u_sum_{j}'; v = f'decoded_v_sum_{j}'
        assert definitions[first] == [first, '+', u, 'center_word']
        assert definitions[second] == [second, '+', v, 'center_word']
        descriptions[first] = {'semantic_sum': [u, 'center_word']}
        descriptions[second] = {'semantic_sum': [v, 'center_word']}
        shift = f'left_form_shift_{j}'; pair = f'left_form_pair_{j}'
        assert definitions[shift] == [shift, '*', 'lane_scale', second]
        assert definitions[pair] == [pair, '+', shift, first]
        consumer_changes[shift] = [shift, '*', 'lane_scale', v]
        consumer_changes[pair] = [f'left_form_uncentered_{j}' if route == 'uniform' else pair, '+', shift, u]
    if route == 'collected':
        parent_shift = definitions['left_six_high_shift_b']
        assert parent_shift == ['left_six_high_shift_b', '*', prior['ports']['left_support_P12'], 'left_seven_high_join']
        consumer_changes['left_six_high_shift_b'] = parent_shift[:3] + ['common_center_restored']

    removed = []; rebound = []; literal = []; inserted = []; assembled = []; stages = {}
    old_cursor = 0
    for old_stage, declared in prior['stages'].items():
        source_block = prior['source'][old_cursor:old_cursor + declared['operations']]
        old_cursor += len(source_block)
        assert row_counts(source_block) == declared
        stage = 'sparse_uncentered_input_forms' if old_stage == 'sparse_centered_input_forms' else old_stage
        block = []
        if old_stage == 'repeated_high_left_pack' and route == 'uniform':
            new_row = ['common_center_pair', '*', 'pack_R2', 'center_word']
            block.append(new_row); inserted.append(new_row)
        for old_row in source_block:
            name = old_row[0]
            if name in descriptions:
                removed.append(old_row)
                continue
            if name in consumer_changes:
                replacement = consumer_changes[name]
                block.append(replacement)
                rebound.append({'before': old_row, 'after': replacement})
            else:
                block.append(old_row); literal.append(name)
            if route == 'uniform' and name.startswith('left_form_pair_'):
                j = name.removeprefix('left_form_pair_')
                new_row = [name, '+', f'left_form_uncentered_{j}', 'common_center_pair']
                block.append(new_row); inserted.append(new_row)
            if route == 'collected' and name == 'left_seven_high_join':
                correction = []
                if eta:
                    P8 = 'geom_P8'; R8 = 'geom_R8'
                    assert P8 in definitions and R8 in definitions
                else:
                    P8 = 'common_center_P8'; R8 = 'common_center_R8'
                    correction.extend([[P8, '*', 'pack_P7', 'lane_scale'], [R8, '+', 'pack_R7', 'pack_P7']])
                correction.extend([
                    ['common_center_plus', '+', prior['ports']['selector_power'], P8],
                    ['common_center_difference', '-', prior['ports']['selector_geometric_sum'], R8],
                    ['common_center_shifted', '*', 'center_word', prior['ports']['left_support_P12']],
                    ['common_center_times_plus', '*', 'common_center_shifted', 'common_center_plus'],
                    ['common_center_correction', '*', 'common_center_times_plus', 'common_center_difference'],
                    ['common_center_restored', '+', 'left_seven_high_join', 'common_center_correction']])
                block.extend(correction); inserted.extend(correction)
        assembled.extend(block); stages[stage] = row_counts(block)
    assert old_cursor == len(prior['source'])
    assert row_counts(removed) == {'M': 0, 'A': 2*r, 'operations': 2*r}
    assert len(rebound) == 2*r + int(route == 'collected')
    assert row_counts(inserted) == ({'M': 1, 'A': r, 'operations': 1+r} if route == 'uniform' else {'M': 4-eta, 'A': 4-eta, 'operations': 8-2*eta})

    current = deepcopy(prior)
    del current['pack_power_alias_splice']
    current['source'] = assembled; current['stages'] = stages
    for key in ['centered_input_forms', 'lanes_in_order']:
        current[key] = semantic_rebinding(prior[key], descriptions)
    current['semantic_lane_note'] = 'semantic_product and semantic_sum describe unchanged mathematical lane values using existing producers; they are not executable ports, extra supplied values or charged arithmetic rows. semantic_sum(L,W) preserves the centered form; L alone need not be positive.'
    current['certificate_prefix_rows'] = len(assembled)-68
    current['certificate_ledger'] = row_counts(assembled[:-68])
    current['polynomial_ledger'] = row_counts(assembled)
    assert assembled[-68:] == prior['source'][-68:]
    assert (current['polynomial_ledger']['M'], current['polynomial_ledger']['A']) == {1: (258,551), 2: (286,589), 4: (350,671)}[r]

    supplied = set(current['ordinary_parameters'] + current['positive_auxiliaries'])
    available = set(supplied); edges = {}; roles = Counter(); role_ops = {}
    for label, operator, arg1, arg2 in assembled:
        assert label not in available and operator in ['+', '-', '*']
        edges[label] = []
        for arg in [arg1, arg2]:
            if type(arg) is str:
                assert arg in available and arg not in descriptions
                edges[label].append(arg)
            elif type(arg) is dict:
                assert set(arg) == {'fixed'}
                roles[arg['fixed']] += 1; role_ops[arg['fixed']] = operator
            else:
                assert type(arg) is int
        available.add(label)
    reachable = set(); frontier = [current['output']]
    while frontier:
        label = frontier.pop()
        if label not in reachable:
            reachable.add(label); frontier.extend(edges.get(label, []))
    assert available <= reachable and not set(descriptions).intersection(available)
    assert len(roles) == 6+15*r and set(roles.values()) == {1}
    assert sorted(roles) == prior['static_checks']['named_fixed_roles']
    assert {name: op for name, op in role_ops.items() if op != '*'} == {'gamma': '+'}

    def bind_descriptor(value):
        if type(value) is str:
            assert value in available
        elif type(value) is list:
            for item in value: bind_descriptor(item)
        elif type(value) is dict:
            for item in value.values(): bind_descriptor(item)
        else:
            assert type(value) is int
    for key in ['ports', 'centered_input_forms', 'lanes_in_order', 'selected_center_ports', 'comparisons']:
        bind_descriptor(current[key])
    current['static_checks'] = dict(topology=True, all_computed_live=True, all_supplied_live=True, named_fixed_roles=sorted(roles))
    current['common_center_splice'] = dict(
        route=route, eta=eta, removed_center_rows=removed, rebound_rows=rebound,
        inserted_rows=inserted, literal_retained_row_names=literal,
        semantic_form_descriptors=descriptions, semantic_metadata_fields=['centered_input_forms','lanes_in_order','semantic_lane_note'],
        old_source_digest=record_digest(prior['source']), new_source_digest=record_digest(assembled),
        removed_ledger=row_counts(removed), inserted_ledger=row_counts(inserted),
        stage_rename={'sparse_centered_input_forms':'sparse_uncentered_input_forms'},
        all_other_fields_inherited=True,
        general_unsaved_scope='Saved r1/2/4 all use uniform sharing. Collected r>=8 and eta/support interactions have handwritten general grammar proof, no saved complete example claimed.')
    examples.append(current)

assert [g['r'] for g in examples] == [1,2,4]
assert sum(len(g['source']) for g in examples) == 2705
output = dict(
    status='FROZEN first original common-center metadata composition; never replay',
    emitter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    inputs=[dict(path=str(PARENT),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))],
    generic_ledger=dict(
        domain='r>=1; same canonical fixed recipe and A/B/C power-alias indicators; eta=prefix100 of binary m=8+2r',
        choice='uniform for1<=r<=7, collected forr>=8; uniform wins or ties in small range; r1 trades1A for1M at equal total',
        uniform_certificate='(201+30r+gM-A-B-C)M+(463+40r+gA-B)A',
        uniform_polynomial='(224+30r+gM-A-B-C)M+(508+40r+gA-B)A',
        uniform_operations='732+70r+gM+gA-A-2B-C',
        collected_certificate='(204+30r+gM-A-B-C-eta)M+(467+39r+gA-B-eta)A',
        collected_polynomial='(227+30r+gM-A-B-C-eta)M+(512+39r+gA-B-eta)A',
        collected_operations='739+69r+gM+gA-A-2B-C-2eta',
        saving='max(r-1,2r-8+2eta) relative to complete power-alias parent',
        native_scale_products='4-C',witnesses='96+6r',equations=23,fixed_roles='6+15r',
        geometric_cost=packet['generic_ledger']['geometric_cost']),
    fixed_data_recipe=packet['fixed_data_recipe'], r0_fallback=packet['r0_fallback'], examples=examples,
    execution_scope='Original record-only construction and deletion/rebinding, metadata descriptions, literal hashes, operation labels, topology/fanout/liveness. No saved instruction/coefficient evaluation, symbolic or degree propagation, scientific sampling, saved helper import/replay or build.')
DEST.write_text(json.dumps(output, indent=2)+'\n')
print('PASS sole metadata emission:2705 records,809/875/1021; freeze composer and receipt permanently')
