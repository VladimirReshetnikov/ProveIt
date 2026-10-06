"""Original one-run literal-record audit; no arithmetic-source evaluation.
Frozen after its first run. Never import or replay this file.
"""
import collections
import hashlib
import json
import re
from pathlib import Path

NEW = Path('/tmp/positive7_repeated_pack_compiler_root.json')
OLD = Path('/tmp/positive7_quotient_pair_compose_root.json')
OUT = Path('/tmp/positive7_repeated_pack_static_audit_riemann_first.json')
assert not OUT.exists()
PINS = {
    NEW: '2fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a',
    OLD: 'eda474bec49c4a2e4fef729c1cae8ed01ee940a8b63a56bb1e1d4cf64684f674',
}
objects = {}
for path, expected_sha in PINS.items():
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == expected_sha
    objects[path] = json.loads(raw)
new, old = objects[NEW], objects[OLD]

def compact(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()

def count(records):
    kinds = collections.Counter(row[1] for row in records)
    assert set(kinds) <= {'+', '-', '*'}
    return {'M': kinds['*'], 'A': kinds['+'] + kinds['-'], 'operations': len(records)}

def stages(graph):
    offset = 0
    result = {}
    for name, census in graph['stages'].items():
        stop = offset + census['operations']
        result[name] = graph['source'][offset:stop]
        assert count(result[name]) == census
        offset = stop
    assert offset == len(graph['source'])
    return result

def consumers(records):
    answer = collections.defaultdict(list)
    for name, op, a, b in records:
        for position, operand in enumerate((a, b), start=2):
            if isinstance(operand, str):
                answer[operand].append([name, position])
    return dict(answer)

assert new['fixed_data_recipe'] == old['fixed_data_recipe']
assert new['r0_fallback'] == old['r0_fallback']
assert len(new['examples']) == len(old['examples']) == 3
results = []
for child, parent in zip(new['examples'], old['examples']):
    r, m, ell = parent['r'], parent['m'], parent['ell']
    assert child['r'] == r and m == 8+2*r and ell == 62+6*r
    prior, actual = stages(parent), stages(child)
    previous = {row[0]: row for row in parent['source']}
    current = {row[0]: row for row in child['source']}
    assert len(previous) == len(parent['source']) and len(current) == len(child['source'])
    P, J = parent['ports']['P'], parent['ports']['J']
    widths = [6,6,6,6,7,7,7,7] + [2]*(2*r)
    assert list(map(len, parent['retained_port_labels'])) == widths
    mask_names = ['aggregate_mask'] + ['letter_mask_'+str(i) for i in range(m)]
    mask_definitions = {'aggregate_mask': ['aggregate_mask','*','height_mask',J]}
    for i in range(m):
        key = 'letter_mask_'+str(i)
        mask_definitions[key] = [key, '*', 'cell_mask', 'selector_'+str(i)]
    assert all(previous[n] == row for n, row in mask_definitions.items())
    excluded = set(mask_names)
    for name in previous:
        hit = re.fullmatch(r'(left|right|output)_(shift|join)_(\d+)', name)
        if hit and (hit[1] == 'right' or int(hit[3]) < m):
            excluded.add(name)
    assert not excluded.intersection(current)

    expected = {}
    expected['input_and_mass'] = prior['input_and_mass']
    expected['geometry_without_redundant_masks'] = [a for a in prior['geometry_guard_centers_and_masks'] if a[0] not in excluded]
    expected['shared_centered_input_forms'] = prior['shared_centered_input_forms']
    support = [
        ['scale_square_0','*',P,P],
        ['pack_P3','*','scale_square_0',P],
        ['pack_P6','*','pack_P3','pack_P3'],
        ['pack_P7','*','pack_P6',P],
        ['pack_R2','+',P,1],
        ['pack_R3','+','pack_R2','scale_square_0'],
        ['pack_P3_plus_one','+','pack_P3',1],
        ['pack_R6','*','pack_R3','pack_P3_plus_one'],
        ['pack_R7','+','pack_R6','pack_P6'],
        ['pack_C2','*','cell_mask','pack_R2'],
        ['pack_C6','*','cell_mask','pack_R6'],
        ['pack_C7','*','cell_mask','pack_R7'],
    ]
    assert previous['scale_square_0'] == support[0]
    expected['shared_pack_powers_and_coefficients'] = support
    bits = bin(m)[2:]
    if bits[:3] in ('110', '111'):
        seed, tail = int(bits[:3], 2), bits[3:]
    else:
        assert bits[:2] == '10'
        seed, tail = 2, bits[2:]
    power = 'scale_square_0' if seed == 2 else 'pack_P'+str(seed)
    rep = 'pack_R'+str(seed)
    index = seed
    extension = []
    for bit in tail:
        doubled = index*2
        next_power, factor, next_rep = 'geom_P'+str(doubled), 'geom_factor_'+str(doubled), 'geom_R'+str(doubled)
        extension += [[next_power,'*',power,power],[factor,'+',power,1],[next_rep,'*',rep,factor]]
        index, power, rep = doubled, next_power, next_rep
        if bit == '1':
            extension += [['geom_R'+str(index+1),'+',rep,power],['geom_P'+str(index+1),'*',power,P]]
            index, power, rep = index+1, 'geom_P'+str(index+1), 'geom_R'+str(index+1)
    assert index == m
    expected['selector_power_and_geometric_extension'] = extension
    gm, ga = 2*len(tail)+tail.count('1'), len(tail)+tail.count('1')
    assert count(extension) == {'M':gm,'A':ga,'operations':gm+ga}
    q = 'selector_'+str(m-1)
    prefix = []
    for i in reversed(range(m-1)):
        shifted, joined = 'selector_polynomial_shift_'+str(i), 'selector_polynomial_join_'+str(i)
        prefix += [[shifted,'*',q,P],[joined,'+',shifted,'selector_'+str(i)]]
        q = joined
    expected['shared_selector_polynomial'] = prefix
    expected['two_upper_horner_packs'] = [a for a in prior['three_guarded_packs'] if a[0] not in excluded]
    joins = [['right_tail_sum','+',J,P],['right_tail_product','*','height_mask','right_tail_sum']]
    acc = 'right_tail_product'
    for i in reversed(range(m)):
        size = widths[i]
        shift, lower, joined = 'right_block_shift_'+str(i), 'right_block_lower_'+str(i), 'right_block_join_'+str(i)
        pn = 'scale_square_0' if size == 2 else 'pack_P'+str(size)
        joins += [[shift,'*',acc,pn],[lower,'*','pack_C'+str(size),'selector_'+str(i)],[joined,'+',shift,lower]]
        acc = joined
    joins += [
        ['right_selector_shift','*',acc,power],['right_selector_sum','*',J,rep],['packed_right','+','right_selector_shift','right_selector_sum'],
        ['left_selector_shift','*','left_join_'+str(m),power],['packed_left','+','left_selector_shift',q],
        ['output_selector_shift','*','output_join_'+str(m),power],['packed_output','+','output_selector_shift',q],
    ]
    expected['factored_pack_joins'] = joins
    assert prior['fixed_native_power'][0] == support[0]
    expected['fixed_native_power_after_shared_square'] = prior['fixed_native_power'][1:]
    replacements = dict(zip(parent['ports']['native_packs'], ['packed_left','packed_right','packed_output']))
    expected['complete_native64'] = [[a[0],a[1],*[replacements.get(v,v) if isinstance(v,str) else v for v in a[2:]]] for a in prior['complete_native64']]
    native_changed = [a[0] for a,b in zip(prior['complete_native64'],expected['complete_native64']) if a != b]
    assert native_changed == ['pell_scaled_A','pell_scaled_B','pell_scaled_Z']
    suffix = list(prior)[list(prior).index('complete_native64')+1:]
    for label in suffix:
        expected[label] = prior[label]
    assert list(expected) == list(actual)
    for label in expected:
        assert expected[label] == actual[label], (r,label)
    all_expected = [row for part in expected.values() for row in part]
    assert all_expected == child['source']

    changed_fields = {'source','stages','static_checks','splice','ports','certificate_ledger','polynomial_ledger','certificate_prefix_rows','lanes_in_order'}
    for key in set(parent)-changed_fields:
        assert child[key] == parent[key], (r,key)
    assert set(child)-set(parent) == {'semantic_lane_note','geometric_extension','pack_splice'}
    assert set(parent)-set(child) == {'splice'}
    expected_ports = dict(parent['ports'], native_packs=['packed_left','packed_right','packed_output'], selector_polynomial=q, selector_power=power, selector_geometric_sum=rep)
    assert child['ports'] == expected_ports
    lane_records = [[{'semantic_product':mask_definitions[a][2:]} if isinstance(a,str) and a in mask_definitions else a for a in lane] for lane in parent['lanes_in_order']]
    assert child['lanes_in_order'] == lane_records
    assert len(lane_records) == ell
    assert child['geometric_extension'] == {'seed':seed,'bits':bits,'remaining':tail,'d':len(tail),'e':tail.count('1'),'M':gm,'A':ga}
    annotation = child['pack_splice']
    removed = [a for a in parent['source'] if a[0] in excluded]
    assert annotation['removed_rows'] == removed
    assert annotation['old_mask_semantic_definitions'] == mask_definitions
    assert annotation['moved_first_square'] == support[0]
    assert annotation['native_pack_bindings'] == replacements
    assert annotation['removed_digest'] == compact(removed)
    assert annotation['old_source_digest'] == compact(parent['source'])
    assert annotation['new_source_digest'] == compact(child['source'])
    retained_names = [a[0] for a in child['source'] if a[0] in previous and a == previous[a[0]] and a[0] != 'scale_square_0']
    assert annotation['retained_literal_row_names'] == retained_names
    before_uses, after_uses = consumers(parent['source']), consumers(child['source'])
    boundary = {key:[use for use in before_uses.get(key,[]) if use[0] not in excluded] for key in excluded}
    boundary = {key:uses for key,uses in boundary.items() if uses}
    assert boundary == {key:[[port,3]] for key,port in zip(parent['ports']['native_packs'],native_changed)}
    assert all(after_uses.get(key) is None for key in excluded)
    assert after_uses[q] == [['packed_left',3],['packed_output',3]]
    assert after_uses[power] == [['right_selector_shift',3],['left_selector_shift',3],['output_selector_shift',3]]
    assert after_uses[rep] == [['right_selector_sum',3]]

    supplied = ['x'] + child['positive_auxiliaries']
    assert len(set(supplied)) == len(supplied)
    known, dependencies, roles = set(supplied), {}, collections.Counter()
    for name, op, a, b in child['source']:
        assert name not in known and op in ('+','-','*')
        for operand in (a,b):
            if isinstance(operand,str): assert operand in known, (r,name,operand)
            elif isinstance(operand,dict):
                assert set(operand)=={'fixed'} and isinstance(operand['fixed'],str)
                roles[operand['fixed']] += 1
            else: assert type(operand) is int
        known.add(name); dependencies[name] = [v for v in (a,b) if isinstance(v,str)]
    reachable, pending = set(), [child['output']]
    while pending:
        key = pending.pop()
        if key not in reachable:
            reachable.add(key); pending.extend(dependencies.get(key,[]))
    assert set(dependencies) <= reachable and set(supplied) <= reachable
    assert sorted(roles) == child['static_checks']['named_fixed_roles'] == parent['static_checks']['named_fixed_roles']
    assert len(roles)==6+18*r and set(roles.values())=={1}
    assert child['static_checks']['topology'] and child['static_checks']['all_computed_live'] and child['static_checks']['all_supplied_live']
    assert len(child['comparisons'])==23 and child['equations']==23
    assert child['witnesses']==len(supplied)-1==96+6*r
    finish = prior['single_polynomial_finalizer']
    assert len(finish)==68 and child['source'][-68:]==finish
    assert count(finish)=={'M':23,'A':45,'operations':68}
    pc = ell.bit_length()-1 + bin(ell).count('1')-1
    assert pc == parent['power_cost'] == child['power_cost']
    poly, cert = count(child['source']), count(child['source'][:-68])
    assert poly == child['polynomial_ledger'] == {'M':252+34*r+pc+gm,'A':541+46*r+ga,'operations':793+80*r+pc+gm+ga}
    assert cert == child['certificate_ledger'] == {'M':229+34*r+pc+gm,'A':496+46*r+ga,'operations':725+80*r+pc+gm+ga}
    assert child['certificate_prefix_rows']==len(child['source'])-68
    novel = [a for a in child['source'] if a[0] not in previous]
    assert len(child['source']) == len(retained_names)+len(novel)+1+len(native_changed)
    results.append({'r':r,'rows':len(child['source']),'coverage':{'literal_retained':len(retained_names),'new_records':len(novel),'relocated_square':1,'rebound_native_headers':len(native_changed)},'old_removed_rows':len(removed),'removed_mask_names':mask_names,'removed_private_boundary':boundary,'new_exit_consumers':{key:after_uses[key] for key in ['packed_left','packed_right','packed_output',q,power,rep]},'relocated_square_consumers':after_uses['scale_square_0'],'stage_censuses':child['stages'],'geometric_extension':child['geometric_extension'],'polynomial':poly,'certificate':cert,'positive_witnesses':child['witnesses'],'fixed_roles_and_consumer_counts':dict(sorted(roles.items())),'all_inherited_declarations_equal':True,'semantic_lane_bindings_exact':True,'topology_and_full_liveness':True,'full_expected_source_digest':compact(all_expected)})

assert [x['r'] for x in results] == [1,2,4]
assert sum(x['rows'] for x in results)==2983
result={'status':'PASS','input_pins':{str(p):s for p,s in PINS.items()},'source_arithmetic_evaluated':False,'degree_propagation':False,'saved_helper_replay':False,'saved_rows_checked':2983,'examples':results,'original_checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'saved_rows_checked':2983,'coverage':{key:sum(x['coverage'][key] for x in results) for key in results[0]['coverage']},'examples':[{'r':x['r'],'poly':x['polynomial'],'coverage':x['coverage']} for x in results]},indent=2))
