"""Original metadata-only emission of the three-form positive7 compiler.

Pinned predecessor rows are inert records; no source, coefficient or degree
evaluation occurs. Freeze this helper and its first output; do not replay.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT_NAME='positive7_relator_plane_compose_root.json'
PARENT_PIN='9992a6d5d81265b701e14d84e9a620ad816ee88dc1eadeb85bc13f6bd986c5c7'
LOCAL_NAME='positive7_inverse_pair_action_pascal.json'
LOCAL_PIN='b830a0644ae0b5ba8b04273a3ac445437af0af2c0b522c1caf3078203f7eab02'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def census(rows):
    ops=Counter(row[1] for row in rows)
    return {'M':ops['*'],'A':ops['+']+ops['-'],'operations':len(rows)}


def read(name,pin):
    path=BASE/name;raw=path.read_bytes()
    if sha(raw)!=pin:
        raise ValueError('changed input '+name)
    return json.loads(raw),{'path':str(path),'sha256':pin,'bytes':len(raw)}


def inspect(rows,supplied,final):
    known=set(supplied);edges={};roles=set()
    if len(known)!=len(supplied):
        raise ValueError('duplicate supplied name')
    for name,op,a,b in rows:
        if name in known or op not in ('+','-','*'):
            raise ValueError('bad source definition')
        for value in (a,b):
            if isinstance(value,str):
                if value not in known:
                    raise ValueError('unknown operand '+value)
            elif isinstance(value,dict):
                if set(value)!={'fixed'}:
                    raise ValueError('invalid fixed role')
                roles.add(value['fixed'])
            elif not isinstance(value,int):
                raise ValueError('invalid literal')
        edges[name]=(a,b);known.add(name)
    live=set();pending=[final]
    while pending:
        value=pending.pop()
        if isinstance(value,str) and value not in live:
            live.add(value);pending.extend(edges.get(value,()))
    if set(edges)-live or set(supplied)-live:
        raise ValueError('dead source row or supplied name')
    return {'all_rows_live':True,'all_supplied_live':True,'topologically_closed':True,
            'named_fixed_roles':sorted(roles)}


def build(r,parent,local):
    if r<1:
        raise ValueError('new source requires at least one relator; use pinned r0 fallback')
    m=8+2*r;w=52+6*r;ell=62+8*r
    rowlist=[];owners=[];stage='input_and_mass'

    def emit(name,op,a,b):
        rowlist.append([name,op,a,b]);owners.append(stage);return name

    def total(tag,fields):
        if not fields:
            raise ValueError('empty sum')
        value=fields[0]
        for index,field in enumerate(fields[1:],1):
            value=emit(tag+'_'+str(index),'+',value,field)
        return value

    def fixed(name):
        return {'fixed':name}

    for row in parent['source'][:6]:
        emit(*row)
    histories=['H_'+str(i) for i in range(1,8)]
    terminals=['F_'+str(i) for i in range(1,7)]
    slots=[[2,3,4,5,6,7]]*2+[[1,2,3,4,5,7]]*2+[list(range(1,8))]*4
    slots += [[0,1,2] for _ in range(2*r)]
    selector_hats=['selector_hat_'+str(s) for s in range(m)]
    selection_hats={(s,i):'selection_hat_'+str(s)+'_'+str(i) for s in range(m) for i in slots[s]}

    stage='geometry_bounds_and_masks'
    selectors=[emit('selector_'+str(s),'-',selector_hats[s],1) for s in range(m)]
    selected={key:emit('selected_'+str(key[0])+'_'+str(key[1]),'-',name,1) for key,name in selection_hats.items()}
    J=total('selector_checksum',selectors)
    D=emit('digit_height','+','initial_mass','height_slack')
    B=emit('cell_radix','*',fixed('K'),D)
    bm1=emit('cell_mask','-',B,1)
    pm1=emit('lane_scale_minus_one','*',bm1,J)
    P=emit('lane_scale','+',pm1,1)
    dm1=emit('height_mask','-',D,1)
    mu=emit('aggregate_mask','*',dm1,J)
    h45=emit('subset_pair45','+',histories[3],histories[4])
    h67=emit('subset_pair67','+',histories[5],histories[6])
    S4=emit('subset_mass','+',h45,h67)
    h12=emit('history_pair12','+',histories[0],histories[1])
    h123=emit('history_first_three','+',h12,histories[2])
    S=emit('history_mass_6','+',h123,S4)
    Ztot=total('selected_mass',list(selected.values()))
    MS=emit('weighted_history_mass','*',fixed('form_bound'),S)
    bound0=emit('joint_bound_a','+',MS,Ztot)
    bound=emit('joint_bound','+',bound0,'global_slack')
    masks=[emit('letter_mask_'+str(s),'*',bm1,selectors[s]) for s in range(m)]

    stage='shared_positive_input_forms'
    forms={}
    for j in range(r):
        forms[j]=[]
        for latent in (1,2):
            terms=[emit('form_term_'+str(j)+'_'+str(latent)+'_'+str(i),'*',
                        fixed('form_a_'+str(j)+'_'+str(latent)+'_'+str(i)),histories[i-1])
                   for i in (4,5,6,7)]
            forms[j].append(total('positive_form_'+str(j)+'_'+str(latent),terms))
    lanes=[[selectors[s],J,selectors[s]] for s in range(m)]
    for s in range(m):
        fields={i:histories[i-1] for i in slots[s]} if s<8 else dict(enumerate([S4]+forms[(s-8)//2]))
        lanes += [[fields[i],masks[s],selected[s,i]] for i in slots[s]]
    lanes += [[S,mu,S],[D,dm1,0]]
    if len(lanes)!=ell:
        raise ValueError('wrong lane partition')

    stage='three_formed_packs'
    packs=[]
    for side,label in enumerate(('left','right','output')):
        top=ell-2 if side==2 else ell-1
        acc=lanes[top][side]
        for index in range(top-1,-1,-1):
            shift=emit(label+'_shift_'+str(index),'*',acc,P)
            acc=emit(label+'_join_'+str(index),'+',shift,lanes[index][side])
        packs.append(acc)
    stage='fixed_native_power'
    power=P
    for index,bit in enumerate(bin(ell)[3:]):
        power=emit('scale_square_'+str(index),'*',power,power)
        if bit=='1':
            power=emit('scale_multiply_'+str(index),'*',power,P)

    stage='complete_native64'
    native_start=next(i for i,row in enumerate(parent['source']) if row[0]=='pell_q')
    old_native=parent['source'][native_start:native_start+64]
    for row in [['pell_q','*',16,power],['pell_scaled_A','*',16,packs[0]],
                ['pell_padded_A','+','pell_scaled_A',12],['pell_scaled_B','*',16,packs[1]],
                ['pell_padded_B','+','pell_scaled_B',10],['pell_scaled_Z','*',16,packs[2]],
                ['pell_F3','+','pell_scaled_Z',8]]:
        emit(*row)
    for row in old_native[7:]:
        emit(*row)

    stage='paired_increment_rows'
    for row in local['source']:
        emit(*row)
    increments=list(local['outputs'])
    stage='selected_formed_relator_appends'
    for j in range(r):
        for s in (8+2*j,9+2*j):
            centered=[]
            for latent in (1,2):
                offset=emit('form_offset_'+str(s)+'_'+str(latent),'*',
                            fixed('form_lambda_'+str(j)+'_'+str(latent)),selected[s,0])
                centered.append(emit('signed_selected_form_'+str(s)+'_'+str(latent),'-',selected[s,latent],offset))
            for coord in (4,5,6):
                for latent in (1,2):
                    product=emit('relator_formed_term_'+str(s)+'_'+str(coord)+'_'+str(latent),'*',
                                 fixed('relator_E_'+str(s)+'_'+str(coord)+'_'+str(latent)),centered[latent-1])
                    increments[coord-1]=emit('relator_formed_sum_'+str(s)+'_'+str(coord)+'_'+str(latent),'+',increments[coord-1],product)

    binding=dict(zip(parent['ports']['six_increments'],increments))
    rename=lambda value:binding.get(value,value) if isinstance(value,str) else value
    suffix_start=next(i for i,row in enumerate(parent['source']) if row[0]=='five_increment_sum_1')
    if len(parent['source'])-suffix_start!=121:
        raise ValueError('unexpected parent suffix')
    for index,(name,op,a,b) in enumerate(parent['source'][suffix_start:]):
        stage=('fused_action_postprocessor' if index<33 else
               'recurrence_right_sides' if index<53 else 'single_polynomial_finalizer')
        emit(name,op,rename(a),rename(b))
    pairs=parent['comparisons']
    auxiliaries=histories+terminals+selector_hats+list(selection_hats.values())
    auxiliaries+=['height_slack','global_slack']+[name for name in parent['positive_auxiliaries'] if name.startswith('pell_')]
    checks=inspect(rowlist,['x']+auxiliaries,parent['output'])
    lam=ell.bit_length()+ell.bit_count()-2
    certificate=census(rowlist[:-68])
    if certificate!={'M':277+50*r+lam,'A':550+62*r,'operations':827+112*r+lam}:
        raise ValueError('all-r certificate ledger')
    if len(auxiliaries)!=96+8*r or len(checks['named_fixed_roles'])!=5+22*r:
        raise ValueError('wrong supplied or fixed-role census')
    return {'r':r,'m':m,'selected_ports':w,'ell':ell,'lambda':lam,
            'ordinary_parameters':['x'],'ordinary_domain':'positive integer x',
            'positive_auxiliaries':auxiliaries,'source':rowlist,'output':parent['output'],
            'certificate_prefix_rows':len(rowlist)-68,'comparisons':pairs,
            'retained_port_labels':slots,'relator_port_meanings':{'0':'S4','1':'A1','2':'A2'},
            'lanes_in_order':lanes,'positive_input_forms':forms,
            'ports':dict(parent['ports'],J=J,D=D,B=B,P=P,S=S,S4=S4,Ztot=Ztot,T=power,native_packs=packs,six_increments=increments),
            'certificate_ledger':certificate,'polynomial_ledger':census(rowlist),
            'equations':len(pairs),'witnesses':len(auxiliaries),'static_checks':checks,
            'stages':{name:census([row for row,owner in zip(rowlist,owners) if owner==name]) for name in dict.fromkeys(owners)},
            'parent_suffix_bindings':binding}


def main():
    parent,parent_info=read(PARENT_NAME,PARENT_PIN)
    local,local_info=read(LOCAL_NAME,LOCAL_PIN)
    r0=next(g for g in parent['examples'] if g['r']==0)
    examples=[];counts_only=[]
    for r in (1,2,3,4,8):
        graph=build(r,r0,local)
        counts_only.append({key:graph[key] for key in ('r','m','selected_ports','ell','lambda','certificate_ledger','polynomial_ledger','equations','witnesses')})
        if r in (1,2,4):
            examples.append(graph)
    result={'status':'original metadata-only three-form complete emission PASS',
            'emitter_sha256':sha(Path(__file__).read_bytes()),'inputs':[parent_info,local_info],
            'generic_ledger':{'domain':'r>=1','certificate':'(277+50r+lambda)M+(550+62r)A',
                              'polynomial':'(300+50r+lambda)M+(595+62r)A',
                              'polynomial_operations':'895+112r+lambda(62+8r)',
                              'lambda':'floor(log2 ell)+popcount(ell)-1','positive_witnesses':'96+8r',
                              'equations':23,'fixed_roles':'5+22r'},
            'r0_fallback':{'parent_receipt_sha256':PARENT_PIN,'source_sha256_compact':sha(json.dumps(r0['source'],separators=(',',':')).encode()),
                           'polynomial_operations':903,'positive_witnesses':96,'new_S4_or_weighted_bound_rows':False},
            'fixed_data_recipe':[
                'For each actual relator P, primitive common right invariant w=(2q,p-t,-2s) supplies an integer row-plane basis u,v; central P=+/-I uses u=e1,v=e2 and E+=E-=0.',
                'Undo any fixed coordinate permutation in u,v before composing C; choose integer E+ and E- with S(P^+/-1)-I=E+/-*[u;v].',
                'For Lj=(u or v)*C on H4,H5,H6,H7, lambda_j=1+max(0,-min coefficient) and form_a=Lj+lambda_j, all positive integers.',
                'form_bound M>=1 is a fixed bound for every positive form coefficient; K is fixed dyadic greater than m, common positive column sum Cmass, and3M+1.',
                'form_a,form_lambda,relator_E and form_bound are linked fixed numerals, not witnesses or independent parameters.',
                'The same full-alphabet positive7 lift supplies kappa_minus_one, and inherited program slice supplies alpha,gamma.',
                'Shared selected form order is S4,A1,A2 per signed relator slot; paired raw52 slots unchanged.',
                'Projection equivalence requires simultaneous state/form digit proof and weighted global bound; no same-witness identity with the old interface is claimed.'],
            'static_shape_censuses':counts_only,'examples':examples,
            'execution_scope':{'metadata_only':True,'source_or_coefficient_arithmetic':False,'degree_propagation':False,
                               'frozen_helper_execution_or_import':False,'numerical_universal_data_supplied':False}}
    output=Path('/tmp/positive7_three_form_compiler_root.json')
    if output.exists():
        raise ValueError('refuse overwrite')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'sha256':sha(output.read_bytes()),'saved_rows':sum(len(g['source']) for g in examples),
                      'counts':counts_only},indent=2))


if __name__=='__main__':
    main()
