"""Original metadata-only record validator; run once, then freeze.

Checks literal tuples and graph properties. No arithmetic source instruction
is executed or symbolically evaluated. No prior helper is imported.
"""
import json
import hashlib
from pathlib import Path
from collections import Counter,defaultdict

TMP=Path('/tmp')
inputs={
 'positive7_guarded_two_form_compiler_root.json':'99e59b73bf1e6a9b0810f8ed862fefe62af00842edafd216e1c0420881ea7784',
 'positive7_three_form_compiler_root.json':'8c056b9fc7b75c79677332e5dafac8de7130a2530cc79ae2fc300c862efed195',
}
objects={}
for filename,digest in inputs.items():
    raw=(TMP/filename).read_bytes();assert hashlib.sha256(raw).hexdigest()==digest
    objects[filename]=json.loads(raw)
new=objects['positive7_guarded_two_form_compiler_root.json']
old=objects['positive7_three_form_compiler_root.json']
parent=old['examples'][0];assert parent['r']==1
parent_rows=parent['source']
def section(start,length):
    i=next(i for i,row in enumerate(parent_rows) if row[0]==start)
    return parent_rows[i:i+length]
native=section('pell_q',64)
# Obtain the paired boundary independently from its first predecessor stage.
paired_start=next(i for i,row in enumerate(parent_rows) if row[0]==native[-1][0])+1
paired=parent_rows[paired_start:paired_start+198]
assert paired[-1][0]=='out_f'
post=section('five_increment_sum_1',33)
rhs=section('terminal_product_F_1',20)
native_aux=[name for name in parent['positive_auxiliaries'] if name.startswith('pell_')]
assert len(native_aux)==21
def count(records):
    c=Counter(row[1] for row in records)
    assert set(c)<=set('+-*')
    return {'M':c['*'],'A':c['+']+c['-'],'operations':len(records)}
def const(name):return {'fixed':name}

reports=[]
for graph in new['examples']:
    r=graph['r'];m=8+2*r;n=52+4*r;ell=62+6*r
    rows=graph['source'];actual={row[0]:row for row in rows}
    assert len(actual)==len(rows)
    need={};owners={}
    def require(stage,record):
        name=record[0];assert name not in need
        need[name]=record;owners[name]=stage
    def prior(stage,records,rename=None):
        rename=rename or {}
        for name,op,a,b in records:
            require(stage,[name,op,rename.get(a,a) if type(a) is str else a,rename.get(b,b) if type(b) is str else b])
    def require_sum(stage,label,fields):
        for k in range(1,len(fields)):
            require(stage,[label+'_'+str(k),'+',fields[0] if k==1 else label+'_'+str(k-1),fields[k]])
        return label+'_'+str(len(fields)-1)
    prior('input_and_mass',parent_rows[:6])
    hist=['H_'+str(i) for i in range(1,8)]
    terminal=['F_'+str(i) for i in range(1,7)]
    slots=[[2,3,4,5,6,7],[2,3,4,5,6,7],[1,2,3,4,5,7],[1,2,3,4,5,7]]+[list(range(1,8)) for _ in range(4)]+[[1,2] for _ in range(2*r)]
    assert graph['retained_port_labels']==slots
    sel=['selector_'+str(s) for s in range(m)]
    selected=['selected_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]]
    sh=['selector_hat_'+str(s) for s in range(m)]
    zh=['selection_hat_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]]
    geom='geometry_guard_centers_and_masks'
    for raw,hat in zip(sel+selected,sh+zh):require(geom,[raw,'-',hat,1])
    J=require_sum(geom,'selector_checksum',sel)
    for record in [
      ['digit_height','+','initial_mass','height_slack'],['cell_radix','*',const('K'),'digit_height'],
      ['cell_mask','-','cell_radix',1],['lane_scale_minus_one','*','cell_mask',J],
      ['lane_scale','+','lane_scale_minus_one',1],['height_mask','-','digit_height',1],
      ['aggregate_mask','*','height_mask',J],
    ]:require(geom,record)
    S=require_sum(geom,'history_mass',hist);Z=require_sum(geom,'selected_mass',selected)
    for record in [
      ['center_height','*',const('center_lambda'),'digit_height'],['center_word','*','center_height',J],
      ['height_repunit','*','digit_height',J],['guard_mass_gap','-','height_repunit',S],
      ['joint_bound','*',const('guard_bound'),'guard_mass_gap'],['joint_rhs','+',Z,'global_slack'],
    ]:require(geom,record)
    for s in range(m):require(geom,['letter_mask_'+str(s),'*','cell_mask',sel[s]])
    forms={}
    for j in range(r):
        forms[str(j)]=[]
        for a in [1,2]:
            terms=[]
            for i in [4,5,6,7]:
                name=f'signed_form_term_{j}_{a}_{i}';terms.append(name)
                require('shared_centered_input_forms',[name,'*',const(f'form_ell_{j}_{a}_{i}'),hist[i-1]])
            dot=require_sum('shared_centered_input_forms',f'signed_form_sum_{j}_{a}',terms)
            port=f'centered_form_{j}_{a}'
            require('shared_centered_input_forms',[port,'+',dot,'center_word']);forms[str(j)].append(port)
    assert graph['centered_input_forms']==forms
    lane_words=[[s,J,s] for s in sel]
    for s,indices in enumerate(slots):
        for i in indices:
            field=hist[i-1] if s<8 else forms[str((s-8)//2)][i-1]
            lane_words.append([field,f'letter_mask_{s}',f'selected_{s}_{i}'])
    lane_words += [[S,'aggregate_mask',S],['digit_height','height_mask',0]]
    assert graph['lanes_in_order']==lane_words and len(lane_words)==ell
    for side,label in enumerate(['left','right','output']):
        high=ell-2 if side==2 else ell-1
        for k in range(high-1,-1,-1):
            first=lane_words[high][side] if k==high-1 else f'{label}_join_{k+1}'
            require('three_guarded_packs',[f'{label}_shift_{k}','*',first,'lane_scale'])
            require('three_guarded_packs',[f'{label}_join_{k}','+',f'{label}_shift_{k}',lane_words[k][side]])
    chain_previous='lane_scale';chain_names=[]
    for k,bit in enumerate(format(ell,'b')[1:]):
        name=f'scale_square_{k}'
        require('fixed_native_power',[name,'*',chain_previous,chain_previous]);chain_previous=name;chain_names.append(name)
        if bit=='1':
            name=f'scale_multiply_{k}'
            require('fixed_native_power',[name,'*',chain_previous,'lane_scale']);chain_previous=name;chain_names.append(name)
    for record in [
      ['pell_q','*',16,chain_previous],['pell_scaled_A','*',16,'left_join_0'],['pell_padded_A','+','pell_scaled_A',12],
      ['pell_scaled_B','*',16,'right_join_0'],['pell_padded_B','+','pell_scaled_B',10],
      ['pell_scaled_Z','*',16,'output_join_0'],['pell_F3','+','pell_scaled_Z',8],
    ]:require('complete_native64',record)
    prior('complete_native64',native[7:]);prior('paired_increment_rows',paired)
    paired_out=['out_a','out_b','joint_C0','out_d','out_e','out_f']
    last=list(paired_out);offsets={}
    for s in range(8,m):
        off=f'selected_center_{s}';offsets[str(s)]=off
        require('selected_guarded_relator_appends',[off,'*','center_height',sel[s]])
        for a in [1,2]:require('selected_guarded_relator_appends',[f'signed_selected_form_{s}_{a}','-',f'selected_{s}_{a}',off])
        for i in [4,5,6]:
            for a in [1,2]:
                term=f'relator_guarded_term_{s}_{i}_{a}';out=f'relator_guarded_sum_{s}_{i}_{a}'
                require('selected_guarded_relator_appends',[term,'*',const(f'relator_E_{s}_{i}_{a}'),f'signed_selected_form_{s}_{a}'])
                require('selected_guarded_relator_appends',[out,'+',last[i-1],term]);last[i-1]=out
    assert graph['selected_center_ports']==offsets
    rename=dict(zip(parent['ports']['six_increments'],last))
    assert graph['parent_suffix_bindings']==rename
    prior('fused_action_postprocessor',post,rename);prior('recurrence_right_sides',rhs)
    comparisons=[['joint_bound','joint_rhs']]+parent['comparisons'][1:]
    assert graph['comparisons']==comparisons and len(comparisons)==23
    squares=[]
    for k,(left,right) in enumerate(comparisons):
        residual=f'comparison_residual_{k}';square=f'comparison_square_{k}'
        require('single_polynomial_finalizer',[residual,'-',left,right])
        require('single_polynomial_finalizer',[square,'*',residual,residual]);squares.append(square)
    output=require_sum('single_polynomial_finalizer','comparison_sum',squares)
    assert graph['output']==output
    assert actual==need
    aux=hist+terminal+sh+zh+['height_slack','global_slack']+native_aux
    assert graph['positive_auxiliaries']==aux and len(aux)==96+6*r
    assert graph['ordinary_parameters']==['x'] and graph['ordinary_domain']=='positive integer x'
    supplied=['x']+aux;known=set(supplied);edges={};consumers=defaultdict(list);fixed_uses=defaultdict(list)
    assert len(known)==len(supplied)
    for name,op,a,b in rows:
        assert name not in known and op in ['+','-','*']
        for pos,value in enumerate([a,b]):
            if type(value) is str:assert value in known;consumers[value].append([name,pos])
            elif type(value) is dict:assert set(value)=={'fixed'};fixed_uses[value['fixed']].append([name,pos])
            else:assert type(value) is int
        edges[name]=[a,b];known.add(name)
    live=set();pending=[output]
    while pending:
        item=pending.pop()
        if type(item) is str and item not in live:live.add(item);pending.extend(edges.get(item,[]))
    assert set(edges)<=live and set(supplied)<=live
    roles={'alpha','gamma','K','kappa_minus_one','center_lambda','guard_bound'}
    roles.update(f'form_ell_{j}_{a}_{i}' for j in range(r) for a in [1,2] for i in [4,5,6,7])
    roles.update(f'relator_E_{s}_{i}_{a}' for s in range(8,m) for i in [4,5,6] for a in [1,2])
    assert set(fixed_uses)==roles and all(len(v)==1 for v in fixed_uses.values()) and len(roles)==6+20*r
    assert graph['static_checks']['named_fixed_roles']==sorted(roles)
    assert consumers['center_height']==[['center_word',0]]+[[f'selected_center_{s}',0] for s in range(8,m)]
    assert consumers['center_word']==[[f'centered_form_{j}_{a}',1] for j in range(r) for a in [1,2]]
    for s in range(8,m):assert consumers[f'selected_center_{s}']==[[f'signed_selected_form_{s}_{a}',1] for a in [1,2]]
    assert consumers['joint_bound']==[['comparison_residual_0',0]] and consumers['joint_rhs']==[['comparison_residual_0',1]]
    assert graph['relator_port_meanings']=={'1':'selected centered form A1','2':'selected centered form A2'}
    ports={k:v for k,v in parent['ports'].items() if k!='S4'}
    ports.update(J=J,D='digit_height',B='cell_radix',P='lane_scale',S=S,Ztot=Z,T=chain_previous,native_packs=['left_join_0','right_join_0','output_join_0'],six_increments=last,center_height='center_height',center_word='center_word',DJ='height_repunit',guard_comparison=['joint_bound','joint_rhs'])
    assert graph['ports']==ports
    stage_names=list(graph['stages']);stage_positions=[stage_names.index(owners[row[0]]) for row in rows]
    assert stage_positions==sorted(stage_positions)
    stage_counts={stage:count([row for row in rows if owners[row[0]]==stage]) for stage in stage_names}
    assert stage_counts==graph['stages']
    p=len(format(ell,'b'))+format(ell,'b').count('1')-2
    assert p==len(chain_names)==graph['power_cost']
    assert count(rows[:-68])==graph['certificate_ledger']==dict(M=280+42*r+p,A=550+54*r,operations=830+96*r+p)
    assert count(rows)==graph['polynomial_ledger']==dict(M=303+42*r+p,A=595+54*r,operations=898+96*r+p)
    assert graph['certificate_prefix_rows']==len(rows)-68 and graph['equations']==23 and graph['witnesses']==len(aux)
    assert graph['m']==m and graph['selected_ports']==n and graph['ell']==ell
    boundaries=['center_height','center_word','height_repunit','guard_mass_gap','joint_bound','joint_rhs',S,Z,'global_slack','lane_scale',chain_previous,'terminal_product_F_1']
    boundaries += [port for pair in forms.values() for port in pair]+list(offsets.values())
    boundaries += [f'selected_{s}_{a}' for s in range(8,m) for a in [1,2]]
    reports.append(dict(r=r,rows=len(rows),certificate=count(rows[:-68]),polynomial=count(rows),witnesses=len(aux),fixed_roles=len(roles),ell=ell,power_cost=p,
      all_rows_literal_matched=True,topology=True,all_rows_live=True,all_supplied_live=True,stage_counts=stage_counts,
      comparisons=comparisons,native_auxiliaries=native_aux,boundary_consumers={name:consumers[name] for name in boundaries},fixed_role_consumers=dict(fixed_uses),suffix_bindings=rename,
      native_rows=64,unchanged_native_core_rows=57,paired_rows=198,copied_fused_and_rhs_rows=53,reconstructed_finalizer_rows=68,
      removed_relator_field_zero=True,removed_old_form_bound_and_offsets=True,complete_lane_partition={'selector':m,'selected':n,'aggregate_and_height':2}))

assert [g['r'] for g in new['examples']]==[1,2,4]
for item in new['static_shape_censuses']:
    r=item['r'];ell=62+6*r;p=len(format(ell,'b'))+format(ell,'b').count('1')-2
    assert item['ell']==ell and item['power_cost']==p and item['witnesses']==96+6*r
    assert item['certificate_ledger']==dict(M=280+42*r+p,A=550+54*r,operations=830+96*r+p)
    assert item['polynomial_ledger']==dict(M=303+42*r+p,A=595+54*r,operations=898+96*r+p)
assert new['r0_fallback']==dict(old['r0_fallback'],inherited_through_three_form_receipt=inputs['positive7_three_form_compiler_root.json'])
receipt={'status':'PASS','inputs':inputs,'scope':'All literal operation records and named dependencies, not their arithmetic values; no saved helper replay or degree propagation.',
 'saved_rows_checked':sum(g['rows'] for g in reports),'examples':reports,'r0_fallback':new['r0_fallback'],'counts_only_not_saved_graphs':[3,8],
 'original_checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
out=TMP/'positive7_guarded_two_form_static_check_riemann_first.json'
assert not out.exists();out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','saved_rows_checked':receipt['saved_rows_checked'],'receipt_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'examples':[{k:g[k] for k in ['r','rows','certificate','polynomial','witnesses','fixed_roles','ell','power_cost']} for g in reports]},indent=2))
