"""New independent record-only auditor for three frozen common-center graphs.
This original program may run once; freeze first result and never replay.
It does not evaluate source arithmetic, coefficients, polynomials or degrees.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import json

OUTPUT = Path('/tmp/positive7_common_center_static_audit_riemann.json')
if OUTPUT.exists():
    raise RuntimeError('The first receipt exists; replay is forbidden')

def check(condition, label):
    if not condition:
        raise ValueError(label)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def rows_hash(rows):
    return digest(json.dumps(rows, separators=(',', ':')).encode())

def labels(rows):
    tags = Counter(row[1] for row in rows)
    check(set(tags) <= {'*', '+', '-'}, 'operation alphabet')
    return dict(M=tags['*'], A=tags['+']+tags['-'], operations=len(rows))

def stage_blocks(graph):
    result = {}; at = 0
    for name, count in graph['stages'].items():
        block = graph['source'][at:at+count['operations']]
        check(labels(block) == count, 'declared stage versus literal records')
        result[name] = block; at += len(block)
    check(at == len(graph['source']), 'stage partition covers full source')
    return result

def paths_to_strings(value, prefix=()):
    if type(value) is str:
        yield prefix, value
    elif type(value) is list:
        for i, item in enumerate(value):
            yield from paths_to_strings(item, prefix+(i,))
    elif type(value) is dict:
        for name, item in value.items():
            yield from paths_to_strings(item, prefix+(name,))

def describe(value, forms):
    if type(value) is str:
        return forms.get(value, value)
    if type(value) is list:
        return [describe(item, forms) for item in value]
    if type(value) is dict:
        return {name: describe(item, forms) for name, item in value.items()}
    return value

pins = [('positive7_power_alias_compiler_root.json', 'e2985ae7fa1754c347261bca096c4d360f263bcbabf58481f7a0e1d305558b2a'), ('positive7_common_center_compiler_root.json', 'ff634059250ac399883ae3311a81354204a84be82b6ae973983e2e9e95b7d6db')]
packets = []; bindings = []
for name, wanted in pins:
    p = Path('/tmp')/name; raw = p.read_bytes()
    check(digest(raw) == wanted, 'frozen input bytes')
    packets.append(json.loads(raw)); bindings.append(dict(path=str(p), sha256=wanted, bytes=len(raw)))
parent, successor = packets
check(set(parent) == set(successor), 'top-level schema')
check(successor['emitter_sha256'] == '5630441e5c9700c1f8578f97a964cc67038f40052703285cf6a701bd48c00e06', 'frozen author emitter pin')
check(successor['fixed_data_recipe'] == parent['fixed_data_recipe'] and successor['r0_fallback'] == parent['r0_fallback'], 'whole fixed recipe and fallback literal')
check([g['r'] for g in parent['examples']] == [1,2,4] == [g['r'] for g in successor['examples']], 'actual example scope')
reports = []
for old, new in zip(parent['examples'], successor['examples']):
    r = old['r']; before = old['source']; after = new['source']
    old_by_name = {row[0]: row for row in before}; new_by_name = {row[0]: row for row in after}
    check(len(old_by_name) == len(before) and len(new_by_name) == len(after), 'unique old/new definitions')
    old_blocks = stage_blocks(old); new_blocks = stage_blocks(new)
    deleted = {}; edits = {}; semantics = {}; old_fanout = {}; pair_fanout = {}
    for j in range(r):
        f1, f2 = f'centered_form_{j}_1', f'centered_form_{j}_2'
        u, v = f'decoded_u_sum_{j}', f'decoded_v_sum_{j}'
        shift, pair, uncentered = f'left_form_shift_{j}', f'left_form_pair_{j}', f'left_form_uncentered_{j}'
        deleted[f1] = [f1, '+', u, 'center_word']; deleted[f2] = [f2, '+', v, 'center_word']
        check(old_by_name[f1] == deleted[f1] and old_by_name[f2] == deleted[f2], 'exact center definitions')
        check(old_by_name[shift] == [shift, '*', 'lane_scale', f2] and old_by_name[pair] == [pair, '+', shift, f1], 'old pair cut')
        edits[shift] = [[shift, '*', 'lane_scale', v]]
        edits[pair] = [[uncentered, '+', shift, u], [pair, '+', uncentered, 'common_center_pair']]
        semantics[f1] = {'semantic_sum':[u,'center_word']}; semantics[f2] = {'semantic_sum':[v,'center_word']}
        for field, consumer in [(f1,pair),(f2,shift)]:
            users = [(row[0],i) for row in before for i,arg in enumerate(row[2:],2) if type(arg) is str and arg == field]
            check(users == [(consumer,3)], 'full removed-form arithmetic fanout'); old_fanout[field] = users
        pair_users = [(row[0],i) for row in before for i,arg in enumerate(row[2:],2) if type(arg) is str and arg == pair]
        check(pair_users == [(f'left_form_repeated_{j}',3)], 'restored pair boundary')
        pair_fanout[pair] = pair_users
    expected = []; retained = []; removed = []; rebound = []; inserted = []
    common = ['common_center_pair','*','pack_R2','center_word']
    for stage, block in old_blocks.items():
        reconstructed = []
        if stage == 'repeated_high_left_pack':
            reconstructed.append(common); inserted.append(common)
        for row in block:
            if row[0] in deleted:
                removed.append(row)
            elif row[0] in edits:
                replacement = edits[row[0]]; reconstructed.extend(replacement)
                rebound.append(dict(before=row,after=replacement[0]))
                inserted.extend(replacement[1:])
            else:
                reconstructed.append(row); retained.append(row[0])
        new_stage = 'sparse_uncentered_input_forms' if stage == 'sparse_centered_input_forms' else stage
        check(new_blocks[new_stage] == reconstructed, 'full independent stage reconstruction')
        expected.extend(reconstructed)
    check(list(new_blocks) == ['sparse_uncentered_input_forms' if x == 'sparse_centered_input_forms' else x for x in old_blocks], 'stage order and rename')
    check(after == expected, 'every successor record and order')
    check((len(retained),len(rebound),len(inserted),len(removed)) == {1:(805,2,2,2),2:(868,4,3,4),4:(1008,8,5,8)}[r], 'disjoint coverage')
    changed = {'source','stages','centered_input_forms','lanes_in_order','semantic_lane_note','certificate_prefix_rows','certificate_ledger','polynomial_ledger','static_checks','pack_power_alias_splice','common_center_splice'}
    check(set(new) == (set(old)-{'pack_power_alias_splice'})|{'common_center_splice'}, 'example schema')
    for field in set(old)-changed:
        check(new[field] == old[field], 'literal inherited field '+field)
    metadata_sites = {}
    for field in ('centered_input_forms','lanes_in_order'):
        metadata_sites[field] = [dict(path=list(path),removed=value) for path,value in paths_to_strings(old[field]) if value in deleted]
        check(new[field] == describe(old[field],semantics), 'exact semantic descriptor substitution')
        check(len(metadata_sites[field]) == (2*r if field == 'centered_input_forms' else 4*r), 'all semantic form occurrences')
    note = 'semantic_product and semantic_sum describe unchanged mathematical lane values using existing producers; they are not executable ports, extra supplied values or charged arithmetic rows. semantic_sum(L,W) preserves the centered form; L alone need not be positive.'
    check(new['semantic_lane_note'] == note, 'semantic not executable note')
    supplied = new['ordinary_parameters']+new['positive_auxiliaries']; available=set(supplied); edges={}; roles=defaultdict(list)
    check(len(supplied) == len(available) and not available.intersection(new_by_name), 'input uniqueness')
    for name, op, lhs, rhs in after:
        check(type(name) is str and name not in available and op in ('+','-','*'), 'record grammar')
        edges[name]=[]
        for slot,arg in enumerate((lhs,rhs),2):
            if type(arg) is str:
                check(arg in available and arg not in deleted, 'topological consumer binding'); edges[name].append(arg)
            elif type(arg) is dict:
                check(set(arg)=={'fixed'} and type(arg['fixed']) is str, 'fixed role schema')
                roles[arg['fixed']].append(dict(consumer=name,operator=op,operand_index=slot))
            else:
                check(type(arg) is int, 'literal type')
        available.add(name)
    reached=set(); todo=[new['output']]
    while todo:
        value=todo.pop()
        if value not in reached:
            reached.add(value); todo.extend(edges.get(value,[]))
    check(available <= reached and not set(deleted).intersection(available), 'all supplied/computed live and retired registers absent')
    check(set(roles)==set(old['static_checks']['named_fixed_roles']) and len(roles)==6+15*r and all(len(v)==1 for v in roles.values()), 'all fixed roles unchanged and paid once')
    check({k:v for k,v in roles.items() if v[0]['operator']!='*'} == {'gamma':[dict(consumer='program_tau',operator='+',operand_index=3)]}, 'gamma addition exception')
    check(new['static_checks']==dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(roles)), 'author static flags independently certified')
    for field in ('ports','centered_input_forms','lanes_in_order','selected_center_ports','comparisons'):
        for path,value in paths_to_strings(new[field]):
            check(value in available and value not in deleted, 'all metadata references bind')
    check(new['ordinary_parameters']==['x'] and len(new['positive_auxiliaries'])==new['witnesses']==96+6*r, 'positive input/witness interface')
    check(sum(name.startswith('pell_') for name in supplied)==21 and new['ell']==len(new['lanes_in_order'])==62+6*r, 'native auxiliary and lane counts')
    check(new['comparisons']==old['comparisons'] and new['equations']==len(new['comparisons'])==23, 'complete literal comparisons')
    check(new_blocks['complete_native64']==old_blocks['complete_native64'] and labels(new_blocks['complete_native64'])==dict(M=33,A=31,operations=64), 'literal full native certificate')
    check(new['ports']['T']=='native_shared_scale' and new['native_scale_products']==4 and new_by_name['pell_q']==['pell_q','*',16,'native_shared_scale'], 'unchanged native scale header')
    check(after[-68:]==before[-68:]==new_blocks['single_polynomial_finalizer'] and labels(after[-68:])==dict(M=23,A=45,operations=68), 'complete literal finalizer')
    check(new['output']=='comparison_sum_22' and new['ports']['terminal']==['F_1','F_2','F_3','F_4','F_5','F_6','F_1'], 'endpoint and final output')
    check(new['certificate_prefix_rows']==len(after)-68 and new['certificate_ledger']==labels(after[:-68]) and new['polynomial_ledger']==labels(after), 'all actual operation censuses')
    check((labels(after)['M'],labels(after)['A'])=={1:(258,551),2:(286,589),4:(350,671)}[r], 'independent target full counts')
    expected_splice=dict(route='uniform',eta=int(r==4),removed_center_rows=removed,rebound_rows=rebound,inserted_rows=inserted,literal_retained_row_names=retained,semantic_form_descriptors=semantics,semantic_metadata_fields=['centered_input_forms','lanes_in_order','semantic_lane_note'],old_source_digest=rows_hash(before),new_source_digest=rows_hash(after),removed_ledger=labels(removed),inserted_ledger=labels(inserted),stage_rename={'sparse_centered_input_forms':'sparse_uncentered_input_forms'},all_other_fields_inherited=True,general_unsaved_scope='Saved r1/2/4 all use uniform sharing. Collected r>=8 and eta/support interactions have handwritten general grammar proof, no saved complete example claimed.')
    check(new['common_center_splice']==expected_splice, 'entire author splice receipt')
    reports.append(dict(r=r,full_rows=len(after),literal_rows=len(retained),rebound_rows=rebound,inserted_rows=inserted,removed_rows=removed,old_center_fanout=old_fanout,restored_pair_fanout=pair_fanout,semantic_form_descriptors=semantics,changed_metadata_sites=metadata_sites,stages=new['stages'],certificate_ledger=labels(after[:-68]),polynomial_ledger=labels(after),source_digest=rows_hash(after),fixed_role_uses=dict(roles),positive_witnesses=new['witnesses'],topology_liveness_and_all_fields=True))
check(sum(g['full_rows'] for g in reports)==2705, 'complete total rows')
receipt=dict(status='FROZEN first original independent record audit PASS; never replay',auditor_sha256=digest(Path(__file__).read_bytes()),inputs=bindings,coverage=dict(full_rows=2705,literal_rows=2681,rebound_rows=14,inserted_rows=10,deleted_parent_rows=14),examples=reports,fixed_recipe_and_r0_fallback_literal=True,generic_ledger_scope='Declared all-r formulas and collected branch are hand-reviewed separately, not inferred from these three uniform saved graphs.',execution_scope='Fresh original literal-record construction/comparison, source/name hashes, operation and role counts, topology/fanout/liveness and semantic-descriptor references only. No evaluation of saved arithmetic or coefficient instructions, symbolic or degree propagation, scientific sampling, saved helper execution/import, or build.')
OUTPUT.write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS first independent common-center audit:2705 =2681 literal+14 rewritten+10 inserted;14 deletions;809/875/1021. Freeze auditor and receipt.')
