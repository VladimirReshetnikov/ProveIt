"""Fresh one-run metadata audit. No source/coefficients are evaluated.

Every asserted tuple below is an operation *record*, never an arithmetic
instruction for execution. Frozen author/predecessor code is not imported.
"""
from pathlib import Path
import json
import hashlib
from collections import Counter, defaultdict

ROOT = Path('/tmp')
PINS = {
 'positive7_three_form_compiler_root.json':'8c056b9fc7b75c79677332e5dafac8de7130a2530cc79ae2fc300c862efed195',
 'positive7_relator_plane_compose_root.json':'9992a6d5d81265b701e14d84e9a620ad816ee88dc1eadeb85bc13f6bd986c5c7',
 'positive7_inverse_pair_action_pascal.json':'b830a0644ae0b5ba8b04273a3ac445437af0af2c0b522c1caf3078203f7eab02',
}
def load(name):
    raw=(ROOT/name).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==PINS[name]
    return json.loads(raw)
def census(rows):
    c=Counter(row[1] for row in rows)
    assert set(c)<=set('+-*')
    return dict(M=c['*'],A=c['+']+c['-'],operations=len(rows))
def role(name):
    return {'fixed':name}

new=load('positive7_three_form_compiler_root.json')
old=load('positive7_relator_plane_compose_root.json')
cut=load('positive7_inverse_pair_action_pascal.json')
parent=next(g for g in old['examples'] if g['r']==0)
assert len(cut['source'])==198
native_start=next(i for i,row in enumerate(parent['source']) if row[0]=='pell_q')
parent_native=parent['source'][native_start:native_start+64]
parent_suffix=parent['source'][-121:]
native_aux=[s for s in parent['positive_auxiliaries'] if s.startswith('pell_')]
assert len(native_aux)==21 and len(set(native_aux))==21
assert parent_suffix[0][0]=='five_increment_sum_1'
assert len(parent['comparisons'])==23
fallback=new['r0_fallback']
assert fallback['source_sha256_compact']==hashlib.sha256(json.dumps(parent['source'],separators=(',',':')).encode()).hexdigest()
assert fallback['parent_receipt_sha256']==PINS['positive7_relator_plane_compose_root.json']
assert fallback['polynomial_operations']==len(parent['source'])==903
assert fallback['positive_witnesses']==len(parent['positive_auxiliaries'])==96

results=[]
for graph in new['examples']:
    r=graph['r'];m=8+2*r;nsel=52+6*r;ell=62+8*r
    rows=graph['source'];lookup={row[0]:row for row in rows}
    assert len(lookup)==len(rows)
    checked=[];stage_rows=defaultdict(list)
    def check(name,op,left,right,stage):
        expected=[name,op,left,right]
        assert lookup[name]==expected,(r,name,lookup[name],expected)
        assert name not in checked
        checked.append(name);stage_rows[stage].append(lookup[name])
    def exact(records,stage):
        for record in records:check(*record,stage)
    def chain(prefix,items,stage):
        for i in range(1,len(items)):
            check(prefix+'_'+str(i),'+',items[0] if i==1 else prefix+'_'+str(i-1),items[i],stage)
        return prefix+'_'+str(len(items)-1)
    exact(parent['source'][:6],'input_and_mass')
    H=['H_'+str(i) for i in range(1,8)]
    terminal=['F_'+str(i) for i in range(1,7)]
    paired_slots=[[2,3,4,5,6,7],[2,3,4,5,6,7],[1,2,3,4,5,7],[1,2,3,4,5,7]]+[list(range(1,8)) for _ in range(4)]
    slots=paired_slots+[[0,1,2] for _ in range(2*r)]
    assert graph['retained_port_labels']==slots
    sh=['selector_hat_'+str(s) for s in range(m)]
    rawsel=['selector_'+str(s) for s in range(m)]
    zh=['selection_hat_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]]
    rawz=['selected_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]]
    assert len(rawz)==nsel
    stage='geometry_bounds_and_masks'
    for name,hat in zip(rawsel,sh):check(name,'-',hat,1,stage)
    for name,hat in zip(rawz,zh):check(name,'-',hat,1,stage)
    J=chain('selector_checksum',rawsel,stage)
    exact([
      ['digit_height','+','initial_mass','height_slack'],
      ['cell_radix','*',role('K'),'digit_height'],
      ['cell_mask','-','cell_radix',1],
      ['lane_scale_minus_one','*','cell_mask',J],
      ['lane_scale','+','lane_scale_minus_one',1],
      ['height_mask','-','digit_height',1],
      ['aggregate_mask','*','height_mask',J],
      ['subset_pair45','+','H_4','H_5'],
      ['subset_pair67','+','H_6','H_7'],
      ['subset_mass','+','subset_pair45','subset_pair67'],
      ['history_pair12','+','H_1','H_2'],
      ['history_first_three','+','history_pair12','H_3'],
      ['history_mass_6','+','history_first_three','subset_mass'],
    ],stage)
    Z=chain('selected_mass',rawz,stage)
    exact([
      ['weighted_history_mass','*',role('form_bound'),'history_mass_6'],
      ['joint_bound_a','+','weighted_history_mass',Z],
      ['joint_bound','+','joint_bound_a','global_slack'],
    ],stage)
    for s in range(m):check('letter_mask_'+str(s),'*','cell_mask',rawsel[s],stage)
    form_ports={}
    for j in range(r):
        form_ports[str(j)]=[]
        for a in (1,2):
            terms=['form_term_'+str(j)+'_'+str(a)+'_'+str(i) for i in (4,5,6,7)]
            for i,name in zip((4,5,6,7),terms):
                check(name,'*',role('form_a_'+str(j)+'_'+str(a)+'_'+str(i)),'H_'+str(i),'shared_positive_input_forms')
            port=chain('positive_form_'+str(j)+'_'+str(a),terms,'shared_positive_input_forms')
            form_ports[str(j)].append(port)
    assert graph['positive_input_forms']==form_ports
    lanes=[[s,J,s] for s in rawsel]
    for s in range(m):
        for i in slots[s]:
            field=H[i-1] if s<8 else (['subset_mass']+form_ports[str((s-8)//2)])[i]
            lanes.append([field,'letter_mask_'+str(s),'selected_'+str(s)+'_'+str(i)])
    lanes += [['history_mass_6','aggregate_mask','history_mass_6'],['digit_height','height_mask',0]]
    assert graph['lanes_in_order']==lanes and len(lanes)==ell
    for side,label in enumerate(('left','right','output')):
        last=ell-2 if side==2 else ell-1
        for index in reversed(range(last)):
            higher=lanes[last][side] if index==last-1 else label+'_join_'+str(index+1)
            check(label+'_shift_'+str(index),'*',higher,'lane_scale','three_formed_packs')
            check(label+'_join_'+str(index),'+',label+'_shift_'+str(index),lanes[index][side],'three_formed_packs')
    scale='lane_scale'
    for digit,bit in enumerate(format(ell,'b')[1:]):
        name='scale_square_'+str(digit)
        check(name,'*',scale,scale,'fixed_native_power');scale=name
        if bit=='1':
            name='scale_multiply_'+str(digit)
            check(name,'*',scale,'lane_scale','fixed_native_power');scale=name
    exact([
      ['pell_q','*',16,scale],['pell_scaled_A','*',16,'left_join_0'],
      ['pell_padded_A','+','pell_scaled_A',12],['pell_scaled_B','*',16,'right_join_0'],
      ['pell_padded_B','+','pell_scaled_B',10],['pell_scaled_Z','*',16,'output_join_0'],
      ['pell_F3','+','pell_scaled_Z',8],
    ],'complete_native64')
    exact(parent_native[7:],'complete_native64')
    exact(cut['source'],'paired_increment_rows')
    increments=list(cut['outputs'])
    for s in range(8,m):
        j=(s-8)//2
        for a in (1,2):
            check('form_offset_'+str(s)+'_'+str(a),'*',role('form_lambda_'+str(j)+'_'+str(a)),'selected_'+str(s)+'_0','selected_formed_relator_appends')
            check('signed_selected_form_'+str(s)+'_'+str(a),'-','selected_'+str(s)+'_'+str(a),'form_offset_'+str(s)+'_'+str(a),'selected_formed_relator_appends')
        for i in (4,5,6):
            for a in (1,2):
                term='relator_formed_term_'+str(s)+'_'+str(i)+'_'+str(a)
                accum='relator_formed_sum_'+str(s)+'_'+str(i)+'_'+str(a)
                check(term,'*',role('relator_E_'+str(s)+'_'+str(i)+'_'+str(a)),'signed_selected_form_'+str(s)+'_'+str(a),'selected_formed_relator_appends')
                check(accum,'+',increments[i-1],term,'selected_formed_relator_appends')
                increments[i-1]=accum
    binding=dict(zip(parent['ports']['six_increments'],increments))
    assert graph['parent_suffix_bindings']==binding
    for index,record in enumerate(parent_suffix):
        name,op,a,b=record
        a=binding.get(a,a) if isinstance(a,str) else a
        b=binding.get(b,b) if isinstance(b,str) else b
        stage='fused_action_postprocessor' if index<33 else 'recurrence_right_sides' if index<53 else 'single_polynomial_finalizer'
        check(name,op,a,b,stage)
    assert checked==[row[0] for row in rows]
    assert graph['comparisons']==parent['comparisons']
    assert graph['ordinary_parameters']==['x'] and graph['ordinary_domain']=='positive integer x'
    aux=H+terminal+sh+zh+['height_slack','global_slack']+native_aux
    assert graph['positive_auxiliaries']==aux and len(aux)==96+8*r
    supplied=['x']+aux;known=set(supplied);edges={};consumers=defaultdict(list);role_uses=defaultdict(list)
    assert len(known)==len(supplied)
    for name,op,a,b in rows:
        assert name not in known and op in ('+','-','*')
        for position,value in enumerate((a,b)):
            if isinstance(value,str):
                assert value in known
                consumers[value].append([name,position])
            elif isinstance(value,dict):
                assert set(value)=={'fixed'} and isinstance(value['fixed'],str)
                role_uses[value['fixed']].append([name,position])
            else:assert type(value) is int
        known.add(name);edges[name]=(a,b)
    live=set();pending=[graph['output']]
    while pending:
        item=pending.pop()
        if isinstance(item,str) and item not in live:
            live.add(item);pending.extend(edges.get(item,()))
    assert not set(edges)-live and not set(supplied)-live
    expected_roles={'alpha','gamma','K','kappa_minus_one','form_bound'}
    expected_roles.update('form_a_'+str(j)+'_'+str(a)+'_'+str(i) for j in range(r) for a in (1,2) for i in (4,5,6,7))
    expected_roles.update('form_lambda_'+str(j)+'_'+str(a) for j in range(r) for a in (1,2))
    expected_roles.update('relator_E_'+str(s)+'_'+str(i)+'_'+str(a) for s in range(8,m) for i in (4,5,6) for a in (1,2))
    assert set(role_uses)==expected_roles and len(expected_roles)==5+22*r
    assert sorted(role_uses)==graph['static_checks']['named_fixed_roles']
    for name,uses in role_uses.items():assert len(uses)==(2 if name.startswith('form_lambda_') else 1)
    ports=dict(parent['ports'],J=J,D='digit_height',B='cell_radix',P='lane_scale',S='history_mass_6',S4='subset_mass',Ztot=Z,T=scale,native_packs=['left_join_0','right_join_0','output_join_0'],six_increments=increments)
    assert graph['ports']==ports
    lam=len(format(ell,'b'))+format(ell,'b').count('1')-2
    assert graph['m']==m and graph['ell']==ell and graph['selected_ports']==nsel and graph['lambda']==lam
    assert graph['witnesses']==len(aux) and graph['equations']==23
    assert graph['certificate_prefix_rows']==len(rows)-68
    assert census(rows[:-68])==graph['certificate_ledger']==dict(M=277+50*r+lam,A=550+62*r,operations=827+112*r+lam)
    assert census(rows)==graph['polynomial_ledger']==dict(M=300+50*r+lam,A=595+62*r,operations=895+112*r+lam)
    stages={k:census(v) for k,v in stage_rows.items()}
    assert stages==graph['stages']
    boundaries=['subset_mass','history_mass_6','weighted_history_mass','joint_bound','global_slack','digit_height','lane_scale',scale]
    boundaries += [p for pair in form_ports.values() for p in pair]
    boundaries += ['selected_'+str(s)+'_'+str(i) for s in range(8,m) for i in (0,1,2)]
    results.append(dict(r=r,rows=len(rows),all_rows_literal_matched=True,topology=True,all_rows_live=True,all_supplied_live=True,
      witness_count=len(aux),fixed_role_count=len(role_uses),native_auxiliaries=native_aux,stage_censuses=stages,
      certificate=census(rows[:-68]),polynomial=census(rows),lambda_value=lam,lane_count=ell,
      fixed_role_consumers=dict(role_uses),changed_boundary_consumers={k:consumers[k] for k in boundaries},
      suffix_binding=binding,paired_cut_rows=198,unchanged_native_core_rows=57,complete_native_rows=64,
      unchanged_comparison_pairs=graph['comparisons'],lane_port_partition={'selector':m,'selected':nsel,'aggregate_and_height':2}))
assert [g['r'] for g in new['examples']]==[1,2,4]
for g in new['static_shape_censuses']:
    r=g['r'];ell=62+8*r;lam=len(format(ell,'b'))+format(ell,'b').count('1')-2
    assert g['ell']==ell and g['lambda']==lam and g['witnesses']==96+8*r
    assert g['certificate_ledger']==dict(M=277+50*r+lam,A=550+62*r,operations=827+112*r+lam)
    assert g['polynomial_ledger']==dict(M=300+50*r+lam,A=595+62*r,operations=895+112*r+lam)
out=ROOT/'positive7_three_form_static_audit_riemann_scratch.json'
assert not out.exists()
report={'status':'PASS','scope':'Independent complete literal-row, binding, operation-label, topology and liveness audit; no source or coefficient arithmetic or degree propagation.',
 'input_pins':PINS,'saved_rows_checked':sum(x['rows'] for x in results),'r0_fallback':fallback,
 'counts_only_entries_not_saved_graphs':[3,8],'examples':results,
 'fresh_checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','saved_rows_checked':report['saved_rows_checked'],'output':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'examples':[{k:g[k] for k in ('r','rows','witness_count','fixed_role_count','certificate','polynomial')} for g in results]},indent=2))
