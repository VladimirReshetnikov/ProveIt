"""One-time original metadata emitter; never evaluate arithmetic source rows.

Frozen predecessors are parsed only as inert JSON records. This program
constructs new records and checks names, labels, bindings and liveness.
It must not be executed or imported again after its first receipt exists.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

WIP=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
OUT=Path('/tmp/positive7_guarded_two_form_compiler_root.json')
assert not OUT.exists()
PARENT=WIP/'positive7_three_form_compiler_root.json'
PIN='8c056b9fc7b75c79677332e5dafac8de7130a2530cc79ae2fc300c862efed195'
raw=PARENT.read_bytes()
assert hashlib.sha256(raw).hexdigest()==PIN
old=json.loads(raw)
parent=next(g for g in old['examples'] if g['r']==1)

# Slice by the frozen disjoint stage lengths; no arithmetic row is run.
stages={};cursor=0
for name,count in parent['stages'].items():
    stages[name]=parent['source'][cursor:cursor+count['operations']]
    cursor+=count['operations']
assert cursor==len(parent['source'])
assert len(stages['input_and_mass'])==6
assert len(stages['complete_native64'])==64
assert len(stages['paired_increment_rows'])==198
assert len(stages['fused_action_postprocessor'])==33
assert len(stages['recurrence_right_sides'])==20
assert len(stages['single_polynomial_finalizer'])==68
native_aux=[s for s in parent['positive_auxiliaries'] if s.startswith('pell_')]
assert len(native_aux)==21
paired_outputs=['out_a','out_b','joint_C0','out_d','out_e','out_f']

def counts(rows):
    c=Counter(row[1] for row in rows)
    assert set(c)<=set('+-*')
    return {'M':c['*'],'A':c['+']+c['-'],'operations':len(rows)}

def fixed(name):
    return {'fixed':name}

def build(r):
    assert r>=1
    m=8+2*r;N=52+4*r;ell=62+6*r
    rows=[];groups={};stage='input_and_mass'
    def emit(name,op,a,b):
        row=[name,op,a,b];rows.append(row);groups.setdefault(stage,[]).append(row)
        return name
    def take(records,mapping=None):
        mapping=mapping or {}
        for name,op,a,b in records:
            emit(name,op,mapping.get(a,a) if isinstance(a,str) else a,mapping.get(b,b) if isinstance(b,str) else b)
    def add_chain(name,items):
        acc=items[0]
        for i,item in enumerate(items[1:],1):acc=emit(name+'_'+str(i),'+',acc,item)
        return acc
    take(stages['input_and_mass'])
    H=['H_'+str(i) for i in range(1,8)]
    F=['F_'+str(i) for i in range(1,7)]
    slots=parent['retained_port_labels'][:8]+[[1,2] for _ in range(2*r)]
    selector_hats=['selector_hat_'+str(s) for s in range(m)]
    selector=['selector_'+str(s) for s in range(m)]
    selected_hats=['selection_hat_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]]
    selected=['selected_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]]
    assert len(selected)==N
    stage='geometry_guard_centers_and_masks'
    for raw_name,hat in zip(selector,selector_hats):emit(raw_name,'-',hat,1)
    for raw_name,hat in zip(selected,selected_hats):emit(raw_name,'-',hat,1)
    J=add_chain('selector_checksum',selector)
    D=emit('digit_height','+','initial_mass','height_slack')
    B=emit('cell_radix','*',fixed('K'),D)
    mask=emit('cell_mask','-',B,1)
    emit('lane_scale_minus_one','*',mask,J)
    P=emit('lane_scale','+','lane_scale_minus_one',1)
    dmask=emit('height_mask','-',D,1)
    mu=emit('aggregate_mask','*',dmask,J)
    S=add_chain('history_mass',H)
    Z=add_chain('selected_mass',selected)
    hc=emit('center_height','*',fixed('center_lambda'),D)
    wc=emit('center_word','*',hc,J)
    dj=emit('height_repunit','*',D,J)
    gap=emit('guard_mass_gap','-',dj,S)
    guard_lhs=emit('joint_bound','*',fixed('guard_bound'),gap)
    guard_rhs=emit('joint_rhs','+',Z,'global_slack')
    masks=[emit('letter_mask_'+str(s),'*',mask,selector[s]) for s in range(m)]
    stage='shared_centered_input_forms'
    forms={}
    for j in range(r):
        pair=[]
        for a in (1,2):
            terms=[emit('signed_form_term_'+str(j)+'_'+str(a)+'_'+str(i),'*',fixed('form_ell_'+str(j)+'_'+str(a)+'_'+str(i)),H[i-1]) for i in (4,5,6,7)]
            dot=add_chain('signed_form_sum_'+str(j)+'_'+str(a),terms)
            pair.append(emit('centered_form_'+str(j)+'_'+str(a),'+',dot,wc))
        forms[str(j)]=pair
    lanes=[[s,J,s] for s in selector]
    for s in range(m):
        for i in slots[s]:
            form=H[i-1] if s<8 else forms[str((s-8)//2)][i-1]
            lanes.append([form,masks[s],'selected_'+str(s)+'_'+str(i)])
    lanes.extend([[S,mu,S],[D,dmask,0]])
    assert len(lanes)==ell
    stage='three_guarded_packs'
    pack=[]
    for side,label in enumerate(['left','right','output']):
        last=ell-2 if side==2 else ell-1
        acc=lanes[last][side]
        for i in range(last-1,-1,-1):
            acc=emit(label+'_shift_'+str(i),'*',acc,P)
            acc=emit(label+'_join_'+str(i),'+',acc,lanes[i][side])
        pack.append(acc)
    stage='fixed_native_power'
    scale=P
    for index,bit in enumerate(format(ell,'b')[1:]):
        scale=emit('scale_square_'+str(index),'*',scale,scale)
        if bit=='1':scale=emit('scale_multiply_'+str(index),'*',scale,P)
    power_cost=len(groups[stage])
    stage='complete_native64'
    emit('pell_q','*',16,scale)
    emit('pell_scaled_A','*',16,pack[0]);emit('pell_padded_A','+','pell_scaled_A',12)
    emit('pell_scaled_B','*',16,pack[1]);emit('pell_padded_B','+','pell_scaled_B',10)
    emit('pell_scaled_Z','*',16,pack[2]);emit('pell_F3','+','pell_scaled_Z',8)
    take(stages['complete_native64'][7:])
    stage='paired_increment_rows'
    take(stages[stage])
    increments=list(paired_outputs)
    stage='selected_guarded_relator_appends'
    offset_ports={}
    for s in range(8,m):
        q=emit('selected_center_'+str(s),'*',hc,selector[s]);offset_ports[str(s)]=q
        ts=[emit('signed_selected_form_'+str(s)+'_'+str(a),'-','selected_'+str(s)+'_'+str(a),q) for a in (1,2)]
        for i in (4,5,6):
            for a in (1,2):
                term=emit('relator_guarded_term_'+str(s)+'_'+str(i)+'_'+str(a),'*',fixed('relator_E_'+str(s)+'_'+str(i)+'_'+str(a)),ts[a-1])
                increments[i-1]=emit('relator_guarded_sum_'+str(s)+'_'+str(i)+'_'+str(a),'+',increments[i-1],term)
    binding=dict(zip(parent['ports']['six_increments'],increments))
    stage='fused_action_postprocessor';take(stages[stage],binding)
    stage='recurrence_right_sides';take(stages[stage])
    certificate_rows=len(rows)
    comparisons=[[guard_lhs,guard_rhs]]+parent['comparisons'][1:]
    stage='single_polynomial_finalizer'
    squares=[]
    for k,(a,b) in enumerate(comparisons):
        residual=emit('comparison_residual_'+str(k),'-',a,b)
        squares.append(emit('comparison_square_'+str(k),'*',residual,residual))
    output=add_chain('comparison_sum',squares)
    aux=H+F+selector_hats+selected_hats+['height_slack','global_slack']+native_aux
    supplied=['x']+aux;known=set(supplied);dependencies={};roles=set();consumers={}
    assert len(known)==len(supplied)
    for name,op,a,b in rows:
        assert name not in known and op in ('+','-','*')
        for value in (a,b):
            if isinstance(value,str):
                assert value in known,(name,value)
                consumers.setdefault(value,[]).append(name)
            elif isinstance(value,dict):
                assert set(value)=={'fixed'};roles.add(value['fixed'])
            else:assert type(value) is int
        known.add(name);dependencies[name]=(a,b)
    reachable=set();pending=[output]
    while pending:
        value=pending.pop()
        if isinstance(value,str) and value not in reachable:
            reachable.add(value);pending.extend(dependencies.get(value,()))
    assert set(dependencies)<=reachable and set(supplied)<=reachable
    assert len(aux)==96+6*r and len(comparisons)==23 and len(roles)==6+20*r
    cert=counts(rows[:certificate_rows]);poly=counts(rows)
    assert cert==dict(M=280+42*r+power_cost,A=550+54*r,operations=830+96*r+power_cost)
    assert poly==dict(M=303+42*r+power_cost,A=595+54*r,operations=898+96*r+power_cost)
    ports={k:v for k,v in parent['ports'].items() if k!='S4'}
    ports.update(J=J,D=D,B=B,P=P,S=S,Ztot=Z,T=scale,native_packs=pack,six_increments=increments,center_height=hc,center_word=wc,DJ=dj,guard_comparison=[guard_lhs,guard_rhs])
    return dict(r=r,m=m,selected_ports=N,ell=ell,power_cost=power_cost,ordinary_parameters=['x'],ordinary_domain='positive integer x',positive_auxiliaries=aux,source=rows,output=output,certificate_prefix_rows=certificate_rows,comparisons=comparisons,retained_port_labels=slots,relator_port_meanings={'1':'selected centered form A1','2':'selected centered form A2'},lanes_in_order=lanes,centered_input_forms=forms,selected_center_ports=offset_ports,ports=ports,certificate_ledger=cert,polynomial_ledger=poly,equations=23,witnesses=len(aux),static_checks=dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(roles)),stages={k:counts(v) for k,v in groups.items()},parent_suffix_bindings=binding)

examples=[];censuses=[]
for r in (1,2,3,4,8):
    graph=build(r)
    censuses.append({k:graph[k] for k in ['r','m','selected_ports','ell','power_cost','certificate_ledger','polynomial_ledger','equations','witnesses','stages']})
    if r in (1,2,4):examples.append(graph)
receipt=dict(status='FROZEN first metadata-only emission; never replay this emitter',emitter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),inputs=[dict(path=str(PARENT),sha256=PIN,bytes=len(raw))],generic_ledger=dict(domain='r>=1',certificate='(280+42r+powcost(62+6r))M+(550+54r)A',polynomial='(303+42r+powcost(62+6r))M+(595+54r)A',operations='898+96r+powcost(62+6r)',power_cost='floor(log2 t)+popcount(t)-1',witnesses='96+6r',equations=23,fixed_roles='6+20r'),r0_fallback=dict(old['r0_fallback'],inherited_through_three_form_receipt=PIN),fixed_data_recipe=[
 'Use actual relator integral factorization (S(P^sign)-I)C=E_sign*[ell_1;ell_2] in original coordinates, with prior central +/-I convention.',
 'center_lambda=1+max(0,-all signed ell coefficients), guard_bound=2*center_lambda+1, shared across all relators.',
 'K is fixed dyadic greater than Cmass,m,guard_bound,center_lambda+max(0,all signed ell coefficients).',
 'All signed form_ell and relator_E roles plus positive center_lambda,guard_bound,K follow this one fixed recipe, not independent witnesses.',
 'alpha,gamma and kappa_minus_one retain the inherited program slice and full-alphabet positive7 lift.',
 'Native input positivity and lane bounds follow only at full zeros from the retained global guard. No unconditional form or pack positivity is asserted.',
 'Ordinary-input projection uses simultaneous carry/borrow recovery and positive completion, with new hats, slack, radix and native witnesses.'
],static_shape_censuses=censuses,examples=examples,execution_scope='Constructed/inspected operation records only: no supplied/frozen code import or execution, source/coefficient arithmetic, scalar scientific sampling or degree propagation. Saved full graphs r1,2,4; r3,8 are only structural censuses; r0 refers to unchanged903 predecessor.')
OUT.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(output=str(OUT),sha256=hashlib.sha256(OUT.read_bytes()).hexdigest(),saved_rows=sum(len(g['source']) for g in examples),examples=[{k:g[k] for k in ['r','ell','power_cost','polynomial_ledger','witnesses']} for g in examples]),indent=2))
