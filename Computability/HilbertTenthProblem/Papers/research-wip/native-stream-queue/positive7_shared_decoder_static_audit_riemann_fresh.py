"""Fresh independent record audit, written for one run then frozen.
Inspects JSON records, bindings and counts only; never evaluates an arithmetic row.
"""
import json
import hashlib
from collections import Counter
from pathlib import Path

DEST = Path('/tmp/positive7_shared_decoder_static_audit_riemann_fresh.json')
if DEST.exists():
    raise RuntimeError('First receipt exists: do not replay this auditor')
PARENT = Path('/tmp/positive7_left_scale_compiler_root.json')
CHILD = Path('/tmp/positive7_shared_decoder_compiler_root.json')
PINS = {PARENT: '9a17d38559ae0fc1aac7c987fab827120cdda346fdf2b85fe1b0eb9b1b523d4a',
        CHILD: 'e6539f0c8b8d66b53537d228425932a0a3d030e78d5f96be0d68d513ebe20b95'}

def require(test, why):
    if not test:
        raise ValueError(why)

def hashed(data):
    return hashlib.sha256(data).hexdigest()

def record_hash(value):
    return hashed(json.dumps(value, separators=(',', ':')).encode())

def census(rows):
    tags = Counter(x[1] for x in rows)
    require(set(tags) <= {'*', '+', '-'}, 'unknown instruction tag')
    return {'M': tags['*'], 'A': tags['+'] + tags['-'], 'operations': len(rows)}

packets = []
for path, pin in PINS.items():
    data = path.read_bytes()
    require(hashed(data) == pin, 'input pin mismatch')
    packets.append(json.loads(data))
parent, child = packets
require(set(child) == set(parent), 'top-level schema changed')
require(child['r0_fallback'] == parent['r0_fallback'], 'fallback changed')
require(child['emitter_sha256'] == 'bb333134e85cc6ca8ce11a1469d5c4b0ca95357551f295e7a4bb885ed2319b8f', 'emitter pin')
require(child['inputs'] == [{'path': '/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/positive7_left_scale_compiler_root.json', 'sha256': PINS[PARENT], 'bytes': len(PARENT.read_bytes())}], 'input receipt')
require([x['r'] for x in child['examples']] == [1, 2, 4], 'example index')
require(child['generic_ledger'] == {
    'domain': 'r>=1; same canonical actual-relator recipe throughout',
    'certificate': '(201+30r+gM(8+2r))M+(464+41r+gA(8+2r))A',
    'polynomial': '(224+30r+gM(8+2r))M+(509+41r+gA(8+2r))A',
    'operations': '733+71r+gM(8+2r)+gA(8+2r)', 'native_scale_products': 4,
    'witnesses': '96+6r', 'equations': 23, 'fixed_roles': '6+15r',
    'geometric_cost': parent['generic_ledger']['geometric_cost']}, 'generic ledger')

def split_stages(graph):
    result = {}; offset = 0
    for name, declared in graph['stages'].items():
        rows = graph['source'][offset:offset + declared['operations']]
        require(census(rows) == declared, 'stage count ' + name)
        result[name] = rows; offset += len(rows)
    require(offset == len(graph['source']), 'stage coverage')
    return result

reports = []
for old, new in zip(parent['examples'], child['examples']):
    r = new['r']; old_stages = split_stages(old); new_stages = split_stages(new)
    require(old['r'] == r and new['m'] == 8+2*r and new['ell'] == 62+6*r, 'structural sizes')
    expected_old = []
    for j in range(r):
        for i in (1, 2):
            terms = [f'signed_form_term_{j}_{i}_{k}' for k in (4, 5, 6, 7)]
            expected_old.extend([[terms[k-4], '*', {'fixed': f'form_ell_{j}_{i}_{k}'}, f'H_{k}'] for k in (4, 5, 6, 7)])
            acc = terms[0]
            for index, term in enumerate(terms[1:], 1):
                out = f'signed_form_sum_{j}_{i}_{index}'
                expected_old.append([out, '+', acc, term]); acc = out
            expected_old.append([f'centered_form_{j}_{i}', '+', acc, 'center_word'])
    require(old_stages['shared_centered_input_forms'] == expected_old, 'every old cut record')
    decoder = [['shared_decode_c1', '-', 'H_4', 'H_7'],
               ['shared_decode_k', '-', 'shared_decode_c1', 'H_7'],
               ['shared_decode_c2', '+', 'shared_decode_k', 'H_5'],
               ['shared_decode_k2', '+', 'shared_decode_k', 'shared_decode_k'],
               ['shared_decode_c3', '+', 'shared_decode_k2', 'H_6']]
    forms = []
    for j in range(r):
        forms += [[f'decoded_u_{j}_{i}', '*', {'fixed': f'form_basis_u_{j}_{i}'}, f'shared_decode_c{i}'] for i in (1, 2)]
        forms += [[f'decoded_u_sum_{j}', '+', f'decoded_u_{j}_1', f'decoded_u_{j}_2'],
                  [f'centered_form_{j}_1', '+', f'decoded_u_sum_{j}', 'center_word']]
        forms += [[f'decoded_v_{j}_{i}', '*', {'fixed': f'form_basis_v_{j}_{i}'}, f'shared_decode_c{i}'] for i in (1, 2, 3)]
        forms += [[f'decoded_v_pair_{j}', '+', f'decoded_v_{j}_1', f'decoded_v_{j}_2'],
                  [f'decoded_v_sum_{j}', '+', f'decoded_v_pair_{j}', f'decoded_v_{j}_3'],
                  [f'centered_form_{j}_2', '+', f'decoded_v_sum_{j}', 'center_word']]
    expected_stages = {}
    for name, rows in old_stages.items():
        if name == 'shared_centered_input_forms':
            expected_stages['shared_history_decoder'] = decoder
            expected_stages['sparse_centered_input_forms'] = forms
        else:
            expected_stages[name] = rows
    require(list(expected_stages) == list(new_stages), 'stage order')
    require(expected_stages == new_stages, 'literal all-stage records')
    expected_source = [row for rows in expected_stages.values() for row in rows]
    require(expected_source == new['source'], 'complete row coverage')
    changed_fields = {'source','stages','polynomial_ledger','certificate_ledger','certificate_prefix_rows','static_checks','ports','left_scale_splice','form_decoder_splice'}
    require(set(new) == (set(old)-{'left_scale_splice'})|{'form_decoder_splice'}, 'example schema')
    for key in set(old)-changed_fields:
        require(old[key] == new[key], 'inherited field '+key)
    require(new['ports'] == {**old['ports'], 'decoded_history_fields': ['shared_decode_c1','shared_decode_c2','shared_decode_c3']}, 'all port bindings')
    supplied = new['ordinary_parameters'] + new['positive_auxiliaries']
    require(len(supplied) == len(set(supplied)) and new['ordinary_parameters'] == ['x'], 'supplied names')
    require(len(new['positive_auxiliaries']) == new['witnesses'] == 96+6*r, 'witnesses')
    require(sum(x.startswith('pell_') for x in new['positive_auxiliaries']) == 21, 'native auxiliaries')
    known = set(supplied); definitions = {}; roles = Counter(); consumers = {}
    for row_index, row in enumerate(new['source']):
        require(isinstance(row,list) and len(row)==4, 'row schema')
        name, tag, left, right = row
        require(isinstance(name,str) and name not in known and tag in ('*','+','-'), 'unique definition/operator')
        for slot, operand in enumerate((left,right),2):
            if type(operand) is str:
                require(operand in known, 'forward or missing operand')
                consumers.setdefault(operand,[]).append({'consumer':name,'operand_index':slot})
            elif type(operand) is dict:
                require(set(operand)=={'fixed'} and isinstance(operand['fixed'],str) and tag=='*', 'fixed literal role')
                roles[operand['fixed']] += 1
            else:
                require(type(operand) is int, 'integer literal')
        definitions[name] = (left,right); known.add(name)
    live = set(); pending = [new['output']]
    while pending:
        label = pending.pop()
        if label in live: continue
        live.add(label)
        if label in definitions: pending.extend(x for x in definitions[label] if type(x) is str)
    require(set(definitions)<=live and set(supplied)<=live, 'computed/supplied liveness')
    def bind(value):
        if type(value) is str: require(value in known, 'metadata port label')
        elif type(value) is list:
            for part in value: bind(part)
        elif type(value) is dict:
            for part in value.values(): bind(part)
        else: require(type(value) is int, 'port type')
    bind(new['ports']); bind(new['centered_input_forms']); bind(new['selected_center_ports']); bind(new['lanes_in_order'])
    require(len(new['lanes_in_order'])==new['ell'], 'lane count')
    retired = {f'form_ell_{j}_{i}_{k}' for j in range(r) for i in (1,2) for k in (4,5,6,7)}
    introduced = {f'form_basis_{b}_{j}_{i}' for j in range(r) for b,indices in [('u',(1,2)),('v',(1,2,3))] for i in indices}
    expected_roles = (set(old['static_checks']['named_fixed_roles'])-retired)|introduced
    require(set(roles)==expected_roles and len(roles)==6+15*r and set(roles.values())=={1}, 'exact fixed role census')
    require(new['static_checks']=={'topology':True,'all_computed_live':True,'all_supplied_live':True,'named_fixed_roles':sorted(roles)}, 'static flags')
    exits = {f'centered_form_{j}_{i}' for j in range(r) for i in (1,2)}
    old_names = {row[0] for row in expected_old}; old_outside = [row for row in old['source'] if row[0] not in old_names]
    outside = [row for rows in new_stages.values() for row in rows if row[0] not in {x[0] for x in decoder+forms}]
    require(outside == old_outside, 'all outside records literal')
    fanout = {name:[] for name in sorted(exits)}
    for row in outside:
        for slot,operand in enumerate(row[2:],2):
            if type(operand) is str and operand in old_names:
                require(operand in exits, 'private old temporary escapes')
                fanout[operand].append({'consumer':row[0],'operand_index':slot})
    expected_fanout = {f'centered_form_{j}_{i}':[{'consumer':f'left_form_{"pair" if i==1 else "shift"}_{j}','operand_index':3}] for j in range(r) for i in (1,2)}
    require(fanout==expected_fanout, 'complete external cut consumers')
    require(not ((old_names-exits)&known), 'retired temporary survives')
    require(new_stages['complete_native64']==old_stages['complete_native64'] and len(new_stages['complete_native64'])==64, 'native literal binding')
    final=[]
    require(len(new['comparisons'])==new['equations']==23, 'comparison count')
    for i,(lhs,rhs) in enumerate(new['comparisons']):
        require(lhs in known and rhs in known, 'comparison endpoint')
        final += [[f'comparison_residual_{i}','-',lhs,rhs],[f'comparison_square_{i}','*',f'comparison_residual_{i}',f'comparison_residual_{i}']]
    for i in range(1,23): final.append([f'comparison_sum_{i}','+',f'comparison_square_0' if i==1 else f'comparison_sum_{i-1}',f'comparison_square_{i}'])
    require(final==new['source'][-68:]==old['source'][-68:] and new['output']=='comparison_sum_22', 'exact finalizer')
    require(new['comparisons'][0]==['joint_bound','joint_rhs'] and new['comparisons'][1:16]==old['comparisons'][1:16], 'guard/native comparison order')
    require(new['ports']['terminal']==['F_1','F_2','F_3','F_4','F_5','F_6','F_1'], 'terminal alias')
    require(new['ports']['T']=='native_shared_scale' and new['native_scale_products']==4, 'native scale port')
    require(new['polynomial_ledger']==census(new['source']) and new['certificate_ledger']==census(new['source'][:-68]) and new['certificate_prefix_rows']==len(new['source'])-68, 'ledgers')
    expected_counts={1:(259,553,812),2:(286,592,878),4:(350,676,1026)}[r]
    require(tuple(new['polynomial_ledger'][k] for k in ('M','A','operations'))==expected_counts, 'example full census')
    expected_splice={'removed_rows':expected_old,'removed_digest':record_hash(expected_old),'new_decoder_rows':decoder,'new_form_rows':forms,'literal_retained_row_names':[row[0] for row in old_outside],'old_source_digest':record_hash(old['source']),'new_source_digest':record_hash(new['source']),'unchanged_form_exit_names':sorted(exits),'external_form_consumers':fanout,'retired_fixed_roles':sorted(retired),'introduced_fixed_roles':sorted(introduced),'canonical_recipe_required':True,'finalizer_literal_equal':True,'comparisons_literal_equal':True,'positive_auxiliaries_literal_equal':True,'lanes_literal_equal':True}
    require(new['form_decoder_splice']==expected_splice, 'complete splice metadata')
    reports.append({'r':r,'new_source_rows':len(new['source']),'literal_outside':len(outside),'removed_cut':len(expected_old),'new_decoder':len(decoder),'new_form_records':len(forms),'reused_exit_names':sorted(exits),'external_form_consumers':fanout,'decoder_consumers':{name:consumers[name] for name in [row[0] for row in decoder]},'new_source_digest':record_hash(new['source']),'old_source_digest':record_hash(old['source']),'all_stages':new['stages'],'polynomial_ledger':new['polynomial_ledger'],'certificate_ledger':new['certificate_ledger'],'witnesses':new['witnesses'],'fixed_roles':sorted(roles),'retired_roles':sorted(retired),'introduced_roles':sorted(introduced),'every_row_covered':True,'all_fields_bound':True,'all_live':True})
require(sum(x['new_source_rows'] for x in reports)==2716, 'total rows')
receipt={'status':'FROZEN first successful independent metadata-only audit; never replay','auditor_sha256':hashed(Path(__file__).read_bytes()),'inputs':[{'path':str(p),'sha256':pin,'bytes':len(p.read_bytes())} for p,pin in PINS.items()],'coverage':{'successor_rows':2716,'literal_outside':2631,'removed_parent_cut':112,'replacement_records':85,'external_rebindings':0,'same_named_cut_exits':14},'examples':reports,'fixed_recipe_hand_review':'Canonical first-nonzero transposition ensures original u3=0. Common original-order V binds ell/E/T/J0 and ell-based guard. Recipe text read completely; no coefficient arithmetic executed.','recipe_literal_sha256':record_hash(child['fixed_data_recipe']),'scope':'Every saved row compared structurally to old literal records or fresh handwritten expected cut. Topology, fanout, role/operation counts, live labels, all unchanged fields, native/guard/comparison/finalizer bindings. No numerical or symbolic instruction evaluation, coefficient array evaluation, degree propagation, scientific imports, saved helper replay or build.'}
DEST.write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: all 2716 rows; 2631 literal outside +85 new; no outside rewiring; 812/878/1026 operations. Auditor and first receipt now frozen.')
