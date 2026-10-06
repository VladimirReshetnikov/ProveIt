"""Second, wholly fresh inert graph-map audit; run once and preserve its receipt.
The earlier failed auditor is not an input and is never imported or executed.
No arithmetic instruction, fixed-coefficient array, or polynomial is evaluated.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import json

TARGET = Path('/tmp/positive7_shared_decoder_graphmap_audit_riemann.json')
if TARGET.exists():
    raise RuntimeError('Receipt already exists; no replay permitted')

def check(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(obj):
    return sha(json.dumps(obj, separators=(',', ':')).encode())

def counts(rows):
    mult = sum(row[1] == '*' for row in rows)
    return dict(M=mult, A=len(rows)-mult, operations=len(rows))

bindings = []
data = []
for basename, expected in [
    ('positive7_left_scale_compiler_root', '9a17d38559ae0fc1aac7c987fab827120cdda346fdf2b85fe1b0eb9b1b523d4a'),
    ('positive7_shared_decoder_compiler_root', 'e6539f0c8b8d66b53537d228425932a0a3d030e78d5f96be0d68d513ebe20b95')]:
    path = Path('/tmp') / (basename + '.json'); raw = path.read_bytes()
    check(sha(raw) == expected, 'immutable input')
    bindings.append(dict(path=str(path), sha256=expected, bytes=len(raw)))
    data.append(json.loads(raw))
ancestor, successor = data
check(successor['r0_fallback'] == ancestor['r0_fallback'], 'r0 fallback')
check([g['r'] for g in successor['examples']] == [1,2,4], 'graph inventory')
check(successor['emitter_sha256'] == 'bb333134e85cc6ca8ce11a1469d5c4b0ca95357551f295e7a4bb885ed2319b8f', 'author source pin')

# This is a fresh literal target definition, not a copied or executed helper.
shared = [
    ['shared_decode_c1','-','H_4','H_7'],
    ['shared_decode_k','-','shared_decode_c1','H_7'],
    ['shared_decode_c2','+','shared_decode_k','H_5'],
    ['shared_decode_k2','+','shared_decode_k','shared_decode_k'],
    ['shared_decode_c3','+','shared_decode_k2','H_6']]

outcomes=[]
for old, new in zip(ancestor['examples'], successor['examples']):
    r = new['r']; a = old['source']; b = new['source']
    check(old['r']==r, 'matching graph')
    # Locate both boundary endpoints by literal names, independently of stage metadata.
    ai = {row[0]:i for i,row in enumerate(a)}
    begin = ai['signed_form_term_0_1_4']; end = ai[f'centered_form_{r-1}_2']+1
    check(end-begin==16*r, 'old cut span')
    old_expected=[]; fresh=list(shared)
    for j in range(r):
        for side in (1,2):
            tokens=[]
            for h in range(4,8):
                token=f'signed_form_term_{j}_{side}_{h}'; tokens.append(token)
                old_expected.append([token,'*',{'fixed':f'form_ell_{j}_{side}_{h}'},f'H_{h}'])
            left=tokens[0]
            for number,right in enumerate(tokens[1:],1):
                label=f'signed_form_sum_{j}_{side}_{number}'
                old_expected.append([label,'+',left,right]);left=label
            old_expected.append([f'centered_form_{j}_{side}','+',left,'center_word'])
        for letter,dimensions,sum_names,exit_side in [('u',2,[f'decoded_u_sum_{j}'],1),('v',3,[f'decoded_v_pair_{j}',f'decoded_v_sum_{j}'],2)]:
            products=[f'decoded_{letter}_{j}_{i}' for i in range(1,dimensions+1)]
            for i,product in enumerate(products,1):
                fresh.append([product,'*',{'fixed':f'form_basis_{letter}_{j}_{i}'},f'shared_decode_c{i}'])
            accumulator=products[0]
            for label,other in zip(sum_names,products[1:]):
                fresh.append([label,'+',accumulator,other]);accumulator=label
            fresh.append([f'centered_form_{j}_{exit_side}','+',accumulator,'center_word'])
    check(a[begin:end]==old_expected, 'all old cut records independently reconstructed')
    check(b==a[:begin]+fresh+a[end:], 'complete new source: literal prefix, fresh cut, literal suffix')
    check(len(fresh)==5+10*r, 'replacement size')
    positions={row[0]:i for i,row in enumerate(b)}
    check(len(positions)==len(b), 'unique computed names')
    supplied=new['ordinary_parameters']+new['positive_auxiliaries']; supplied_set=set(supplied)
    check(len(supplied)==len(supplied_set) and not supplied_set.intersection(positions), 'supplied names')
    edges={}; users=defaultdict(list); fixed=defaultdict(list)
    for index,row in enumerate(b):
        check(type(row) is list and len(row)==4 and row[1] in ('+','-','*'), 'instruction schema')
        name,operator=row[:2];deps=[]
        for slot in (2,3):
            arg=row[slot]
            if type(arg) is str:
                check(arg in supplied_set or (arg in positions and positions[arg]<index), 'topological operand')
                deps.append(arg);users[arg].append(dict(consumer=name,operand_index=slot))
            elif type(arg) is dict:
                check(set(arg)=={'fixed'} and type(arg['fixed']) is str, 'fixed numeral schema')
                fixed[arg['fixed']].append(dict(consumer=name,operator=operator,operand_index=slot))
            else:
                check(type(arg) is int, 'integer literal schema')
        edges[name]=deps
    reached=set(); stack=[new['output']]
    while stack:
        x=stack.pop()
        if x not in reached:
            reached.add(x);stack.extend(edges.get(x,[]))
    check(set(positions)|supplied_set <= reached, 'all computed and supplied labels live')
    check(new['ordinary_parameters']==['x'] and new['ordinary_domain']=='positive integer x', 'ordinary input')
    check(len(new['positive_auxiliaries'])==new['witnesses']==96+6*r, 'positive witness count')
    check(len([x for x in supplied if x.startswith('pell_')])==21, 'native positive auxiliary count')
    global_roles={'K','alpha','gamma','center_lambda','guard_bound','kappa_minus_one'}
    basis={f'form_basis_{v}_{j}_{i}' for j in range(r) for v,indices in [('u',(1,2)),('v',(1,2,3))] for i in indices}
    action={f'relator_E_{8+2*j}_{h}_{i}' for j in range(r) for h in (4,5,6) for i in (1,2)}
    quotient={f'quotient_T_{j}_{i}_{k}' for j in range(r) for i in (1,2) for k in (1,2)}
    check(set(fixed)==global_roles|basis|action|quotient and len(fixed)==6+15*r, 'exact fixed role set')
    check(all(len(uses)==1 for uses in fixed.values()), 'one paid occurrence per fixed role')
    nonmultiplicative={key:uses for key,uses in fixed.items() if uses[0]['operator']!='*'}
    check(nonmultiplicative=={'gamma':[dict(consumer='program_tau',operator='+',operand_index=3)]}, 'precise fixed role operation split')
    check(b[positions['program_tau']]==['program_tau','+','program_scaled',{'fixed':'gamma'}], 'retained counterexample row')
    # Every graph field not named here must be literally inherited.
    mutable={'source','stages','polynomial_ledger','certificate_ledger','certificate_prefix_rows','static_checks','ports','left_scale_splice','form_decoder_splice'}
    check(set(new)==set(old)-{'left_scale_splice'}|{'form_decoder_splice'}, 'whole example schema')
    for key in set(old)-mutable:check(new[key]==old[key], 'unchanged field '+key)
    check(new['ports']==dict(old['ports'],decoded_history_fields=['shared_decode_c1','shared_decode_c2','shared_decode_c3']), 'complete port field')
    def port_refs(obj):
        if type(obj) is str:check(obj in positions or obj in supplied_set, 'live port descriptor')
        elif type(obj) is list:
            for part in obj:port_refs(part)
        elif type(obj) is dict:
            for part in obj.values():port_refs(part)
        else:check(type(obj) is int, 'port descriptor type')
    for field in ['ports','centered_input_forms','selected_center_ports','lanes_in_order']:port_refs(new[field])
    check(len(new['lanes_in_order'])==new['ell']==62+6*r and new['m']==8+2*r, 'native lane geometry')
    stage_old={};stage_new={}
    for graph,dst in [(old,stage_old),(new,stage_new)]:
        start=0
        for name,ct in graph['stages'].items():
            stop=start+ct['operations']; rows=graph['source'][start:stop]
            check(counts(rows)==ct, 'independent stage census')
            dst[name]=rows;start=stop
        check(start==len(graph['source']), 'stage partition is complete')
    expected_stage_names=[]
    for name in stage_old:
        if name=='shared_centered_input_forms':expected_stage_names.extend(['shared_history_decoder','sparse_centered_input_forms'])
        else:expected_stage_names.append(name);check(stage_old[name]==stage_new[name], 'outside stages unchanged')
    check(list(stage_new)==expected_stage_names and stage_new['shared_history_decoder']==shared and stage_new['sparse_centered_input_forms']==fresh[5:], 'new stage boundary')
    check(len(stage_new['complete_native64'])==64 and counts(stage_new['complete_native64'])==dict(M=33,A=31,operations=64), 'native full certificate')
    check(len(new['comparisons'])==new['equations']==23 and new['comparisons']==old['comparisons'], 'comparison identity')
    final=[]; previous='comparison_square_0'
    for i,pair in enumerate(new['comparisons']):
        port_refs(pair);res=f'comparison_residual_{i}';sq=f'comparison_square_{i}'
        final.extend([[res,'-',*pair],[sq,'*',res,res]])
    for i in range(1,23):
        name=f'comparison_sum_{i}';final.append([name,'+',previous,f'comparison_square_{i}']);previous=name
    check(final==b[-68:]==a[-68:] and new['output']==previous, 'all residuals/squares/final sums')
    check(new['comparisons'][0]==['joint_bound','joint_rhs'] and new['ports']['T']=='native_shared_scale' and new['native_scale_products']==4, 'guard and native scale bindings')
    check(new['ports']['terminal']==['F_1','F_2','F_3','F_4','F_5','F_6','F_1'], 'terminal F7 alias')
    check(counts(b)==new['polynomial_ledger'] and counts(b[:-68])==new['certificate_ledger'] and new['certificate_prefix_rows']==len(b)-68, 'complete ledgers')
    expected={1:(259,553),2:(286,592),4:(350,676)}[r]
    check((counts(b)['M'],counts(b)['A'])==expected, 'example ledger target')
    exits={f'centered_form_{j}_{i}' for j in range(r) for i in (1,2)};oldnames={row[0] for row in old_expected}
    outsiderows=a[:begin]+a[end:];fan={x:[] for x in sorted(exits)}
    for row in outsiderows:
        for slot in (2,3):
            arg=row[slot]
            if type(arg) is str and arg in oldnames:
                check(arg in exits, 'old private temporary escaped')
                fan[arg].append(dict(consumer=row[0],operand_index=slot))
    for j in range(r):
        check(fan[f'centered_form_{j}_1']==[dict(consumer=f'left_form_pair_{j}',operand_index=3)], 'A1 exit consumer')
        check(fan[f'centered_form_{j}_2']==[dict(consumer=f'left_form_shift_{j}',operand_index=3)], 'A2 exit consumer')
    check(not (oldnames-exits).intersection(positions), 'private old names eliminated')
    retired={f'form_ell_{j}_{i}_{h}' for j in range(r) for i in (1,2) for h in (4,5,6,7)}
    exp_splice=dict(removed_rows=old_expected,removed_digest=encoded(old_expected),new_decoder_rows=shared,new_form_rows=fresh[5:],literal_retained_row_names=[row[0] for row in outsiderows],old_source_digest=encoded(a),new_source_digest=encoded(b),unchanged_form_exit_names=sorted(exits),external_form_consumers=fan,retired_fixed_roles=sorted(retired),introduced_fixed_roles=sorted(basis),canonical_recipe_required=True,finalizer_literal_equal=True,comparisons_literal_equal=True,positive_auxiliaries_literal_equal=True,lanes_literal_equal=True)
    check(new['form_decoder_splice']==exp_splice, 'entire splice receipt')
    check(new['static_checks']==dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(fixed)), 'all static author flags independently reproduced')
    outcomes.append(dict(r=r,source_rows=len(b),literal_outside=len(outsiderows),removed_parent_rows=end-begin,replacement_rows=len(fresh),cut_interval_new=[begin,begin+len(fresh)],source_digest=encoded(b),polynomial_ledger=counts(b),certificate_ledger=counts(b[:-68]),fixed_role_uses=dict(fixed),fixed_role_operation_split=dict(multiplication=5+15*r,addition=1),witnesses=new['witnesses'],complete_external_cut_consumers=fan,decoder_consumers={x[0]:users[x[0]] for x in shared},all_stages=new['stages'],all_rows_fields_bindings_live=True))
check(sum(x['source_rows'] for x in outcomes)==2716 and sum(x['literal_outside'] for x in outcomes)==2631 and sum(x['replacement_rows'] for x in outcomes)==85, 'full disjoint coverage')
receipt=dict(status='FROZEN first run PASS; no replay',auditor_sha256=sha(Path(__file__).read_bytes()),inputs=bindings,results=outcomes,coverage=dict(full_rows=2716,literal_outside=2631,new_rows=85,removed_old_rows=112,reused_exit_names=14,outside_rebindings=0),recipe_text_sha256=encoded(successor['fixed_data_recipe']),scope='Complete inert-record, schema, topology, operation/role census, liveness, full field preservation, fanout, native64/21aux/23comparisons/68finalizer audit. Canonical fixed recipe hand-reviewed separately. No row/coefficient evaluation, symbolic execution, degree propagation, scientific import, frozen-code replay, or build.',failed_attempt_separate='Earlier original auditor is preserved without modification; its false all-roles-multiply guard was never replayed or imported here.')
TARGET.write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS complete 2716-row independent graph-map audit; 2631 literal +85 new; gamma is the sole addition role. Freeze source and receipt.')
