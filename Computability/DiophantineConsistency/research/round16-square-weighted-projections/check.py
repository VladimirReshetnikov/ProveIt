#!/usr/bin/env python3
"""Independent two-profile literal verifier. CODE ONLY/HOLD for full review."""
import argparse, copy, hashlib, importlib.util, json, sys
from collections import Counter
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/'research/round16-square-weighted-source'
SOURCE_SEAL='b40d630005f7e8d682c513cb414b2063a47530dc2051a5b2757833f2e90a1be8'
PROFILES=['plain','weighted']
POLICY=dict(max_support=16,affine_support=None,quadratic_first=False,
            profiles=PROFILES,charts='raw untranslated',pruning=False)
HORN_EDITS=[99,101,103,105,107,109,111,113,115,116,118,120,129,133,142,143,144,157]

def need(ok,why):
    if not ok: raise ValueError(why)
def get(p): return json.loads(p.read_bytes())
def canon(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b): return hashlib.sha256(b).hexdigest()
def sha(x): return digest(canon(x))
def meta(p):
    b=p.read_bytes(); return dict(bytes=len(b),sha256=digest(b))
def inventory(p,skip='INDEX.json'):
    return {str(q.relative_to(p)):meta(q) for q in sorted(p.rglob('*'))
            if q.is_file() and str(q.relative_to(p))!=skip}

def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for n,m in pins['files'].items(): need(meta(ROOT/n)==m,'whole input '+n)
    for n,m in pins['core'].items(): need(meta(HERE/n)==m,'author core '+n)
    for n,m in pins['vendor'].items(): need(meta(HERE/'vendor'/n)==m,'vendor '+n)
    for n,h in pins['closed_dependencies'].items():
        folder=ROOT/n; need(meta(folder/'MANIFEST.json')['sha256']==h,'closed parent '+n)
        declared=get(folder/'MANIFEST.json')['files']; actual=inventory(folder,'MANIFEST.json')
        expected={name:m if isinstance(declared.get(name),dict) else m['sha256'] for name,m in actual.items()}
        need(declared==expected,'whole selected parent inventory '+n)
    need(meta(SOURCE/'MANIFEST.json')['sha256']==SOURCE_SEAL,'accepted source seal')
    if (HERE/'MANIFEST.json').exists():
        need(get(HERE/'MANIFEST.json')['files']==inventory(HERE,'MANIFEST.json'),'closed author packet')
    return meta(HERE/'SOURCE_PINS.json')['sha256']

def support():
    # Sole nonstdlib import; no producer, optimizer or source checker is loaded.
    spec=importlib.util.spec_from_file_location('round16_independent',HERE/'vendor/check_direct.py')
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module

def evaluate(poly,values):
    total=0
    for mon,c in poly.items():
        term=c
        for i in mon: term*=values[i]
        total+=term
    return total

def source_check(A,name,d):
    src=d['source']; need(src==get(SOURCE/'data'/f'{name}.json'),'whole accepted source '+name)
    need(src['domain']=='unrestricted integers','whole integer domain')
    context=get(SOURCE/'data/SOURCE_CONTEXT.json'); maps=get(SOURCE/'data/ROW_MAPS.json')[name]
    need(context['namespace']=='Original source131 indices; ROW_MAPS supplies every active profile index. Certificate tokens/stale addresses are provenance only.','explicit original context namespace')
    atoms=context['frame_atoms']; calls=context['power_calls']
    need(len(atoms)==38 and len(calls)==18 and len(context['seed_data'])==15,'complete source interface census')
    normalized=[A.norm(q['affine']) for q in atoms]
    need(all(A.deg(p)<=1 for p in normalized) and len({sha(A.terms(p)) for p in normalized})==38,'all distinct affine frame atoms')
    need(all(A.norm(q[role]) in normalized for q in calls for role in ['base','exponent','output']),'all54 actual power ports in frame')
    frame=A.add(A.v(245),A.con(-2),*[A.sc(A.mul(p,p),-1) for p in normalized])
    need(context['actual_frame_row']==381 and A.norm(src['residuals'][381])==frame,'complete38-atom frame polynomial')
    preserved=set([381,158,382])
    for family,count in [('request_rows',18),('primary_norm_rows',15),('shared_T_rows',5),('cap_rows',13),('derived_t_recurrence_rows',8),('early_rows',10)]:
        need(len(context[family])==count,'source-context '+family)
        for record in context[family]:
            i=record['index']; need(src['residuals'][i]==record['row'],'whole retained context row '+str(i)); preserved.add(i)
    ordinary={1,3,175,522}|set(range(16,25))|{i for p in calls for role in ['base','exponent','output'] for m in A.norm(p[role]) for i in m}
    ordinary|={i for q in context['seed_data'] for i in q['pair']}|set(context['cap_variables'].values())
    ordinary|=set(maps['new_guard_auxiliary'])|{maps['new_product_root']}
    A.literal(src)
    expected=dict(schema='round16_projection_source_binding_v1',profile=name,source_manifest_sha256=SOURCE_SEAL,
        whole_source_file=meta(SOURCE/'data'/f'{name}.json'),source_context=meta(SOURCE/'data/SOURCE_CONTEXT.json'),
        whole_source_maps=meta(SOURCE/'data/ROW_MAPS.json'),ordinary_witness_maps=meta(SOURCE/'data/WITNESS_MAPS.json'),
        retained_calibration=get(SOURCE/'data/CALIBRATION_BINDING.json'),original_compiler_or_native_program_rerun=False,
        old324_polynomial_or_old327_body_identity=False,interval_triples_fresh_across_reparameterization=True,Hstar_H0_raw_tuple_identity=False)
    need(canon(d['SOURCE_BINDING'])==canon(expected),'whole source and ordinary witness/calibration binding')
    return preserved,ordinary

def horn_check(A,src,dst,c,wm,source_rows,ordinary):
    need(set(c)=={'schema','input_sha256','output_sha256','square_variables','square_roots','product_chain','changes','deleted_rows','guard_variables','new_root','new_row','identity','guard_identity'},'whole Horn certificate header')
    need(c['schema']=='signed_horn_factorization_v1','Horn schema')
    need(c['identity']=='(product(L_i^2))*(B^2+G^2) = (product(L_i))^2*(B^2+G^2)' and c['guard_identity']=='((c-a)^2*(c-b)^2-D^2)^2 = (((c-a)*(c-b))^2-D^2)^2','whole Horn identities')
    need(sorted(q['row'] for q in c['changes'])==HORN_EDITS and len(c['changes'])==18,'exact18 Horn edit rows')
    need(c['deleted_rows']==[117,119] and set(c['guard_variables'])=={'h','old_second_square','g','old_D_square'},'exact Horn removals/private roles')
    need(set(c['square_roots'])=={str(s) for s in c['square_variables']},'complete17 root dictionary')
    need(A.factorization(src,dst,c)==18,'independent whole Horn replay')
    old=[A.norm(r) for r in src['residuals']]; new=[A.norm(r) for r in dst['residuals']]
    sq=c['square_variables']; g=c['guard_variables']; h,u,z,d=(g[k] for k in ['h','old_second_square','g','old_D_square'])
    defs={s:next(i for i,r in enumerate(src['residuals']) if r['label']=='nonnegative_square_difference' and old[i].get((s,))==1) for s in sq}
    pr=next(i for i,p in enumerate(old) if p.get((z,)) in [-1,1] and not any(z in m for m in p if m!=(z,)) and A.solved(p,z)==A.mul(A.v(h),A.v(u)))
    dr=next(i for i,p in enumerate(old) if p.get((d,)) in [-1,1] and not any(d in m for m in p if m!=(d,)))
    targets={s:defs[s] for s in sq[:9]+sq[13:15]+[h,u,sq[11]]}; targets.update({z:pr,d:dr})
    targets.update({v:r for r,v in c['product_chain']}); private=sorted(targets)
    need(not set(private)&ordinary,'Horn preserves every ordinary power/frame/cap/product interface')
    removed=set(c['deleted_rows']); rm={r:i for i,r in enumerate(r for r in range(len(old)+1) if r not in removed)}
    for r in source_rows:
        need(r not in removed and r not in HORN_EDITS and src['residuals'][r]==dst['residuals'][rm[r]],'complete source interface row survives Horn '+str(r))
    forward={v:rm[r] for v,r in targets.items() if v not in {u,d}}; forward[c['new_root']]=len(new)-1
    def rules(ds,rows):
        todo=dict(ds); out=[]
        while todo:
            ready=[]
            for v,r in todo.items():
                f=A.solved(rows[r],v)
                if not {j for m in f for j in m}&set(todo): ready.append((v,r,f))
            need(ready,'acyclic Horn maps'); v,r,f=min(ready,key=lambda q:q[0]); del todo[v]
            out.append(dict(coordinate=v,row=r,restoration=A.terms(f)))
        return out
    fr,rr=rules(forward,new),rules(targets,old)
    preserved=sorted(set(range(len(src['variables'])))-set(private))
    expected=dict(schema='round16_horn_existential_maps_v1',source_sha256=sha(src),factored_sha256=sha(dst),
        preserved_source_coordinates=preserved,overwritten_source_coordinates=private,
        source_to_factored=dict(copy_source_coordinates=list(range(len(src['variables']))),initialize_factored_private_to_zero=sorted({u,d}),restorations=fr),
        factored_to_source=dict(discard_factored_coordinates=[c['new_root']],copy_source_coordinates=list(range(len(src['variables']))),restorations=rr),
        full_old_private_witness_identity_claimed=False,
        inverse_scope='Initialize every actual projection-free factored coordinate, reverse all monic steps, then overwrite obsolete original Horn-private witnesses.')
    need(canon(wm)==canon(expected),'every forward/reverse Horn rule and existential scope')
    need(c['new_root']==len(src['variables']) and len(dst['variables'])==len(src['variables'])+1,'actual fresh Horn root namespace')
    need(not any(i in {u,d} for p in new for m in p for i in m),'two obsolete Horn squares actually free')
    product=A.con(1); squares=A.con(1)
    for i in range(11): product=A.mul(product,A.v(i)); squares=A.mul(squares,A.mul(A.v(i),A.v(i)))
    r,s,D2,B2=map(A.v,[11,12,13,14])
    before=A.add(A.mul(A.mul(r,r),A.mul(s,s)),A.sc(D2,-1)); after=A.add(A.mul(A.mul(r,s),A.mul(r,s)),A.sc(D2,-1))
    need(A.mul(squares,A.add(A.mul(before,before),B2))==A.mul(A.mul(product,product),A.add(A.mul(after,after),B2)),'complete free-coefficient Horn boundary identity')
    fixtures=[]
    for seed in [7,19]:
        original={i:((seed*i+3)%11)-5 for i in range(len(src['variables']))}
        for q in rr: original[q['coordinate']]=evaluate(A.norm(q['restoration']),original)
        factored=dict(original); factored[c['new_root']]=0
        for i in [u,d]: factored[i]=0
        for q in fr: factored[q['coordinate']]=evaluate(A.norm(q['restoration']),factored)
        restored={i:factored[i] for i in range(len(src['variables']))}
        for q in rr: restored[q['coordinate']]=evaluate(A.norm(q['restoration']),restored)
        need(all(original[i]==factored[i]==restored[i] for i in preserved),'all Horn exposed coordinates fixed')
        need(factored[c['new_root']]==original[c['product_chain'][-1][1]],'whole Horn output value')
        need(all(evaluate(old[q['row']],original)==evaluate(old[q['row']],restored)==0 for q in rr),'all original private definitions restored')
        need(all(evaluate(new[q['row']],factored)==0 for q in fr),'all factored private definitions restored')
        for i,p in enumerate(old):
            need(evaluate(p,original)==evaluate(p,restored),'all old residual values after restoration')
            need(i in removed or evaluate(p,original)==evaluate(new[rm[i]],factored),'every actual exposed factored residual')
        fixtures.append(dict(seed=seed,whole_source_rows=len(old),whole_factored_rows=len(new)))
    return dict(edits=18,fresh_root=c['new_root'],private_overwrites=private,preserved_source_coordinates=preserved,fixtures=fixtures)

def census(A,eq,poly,used):
    return dict(variables=len(eq['variables']),rows=len(eq['residuals']),degree=A.deg(poly),monomials=len(poly),
        height=max(map(abs,poly.values()),default=0),row_height=max((abs(c) for r in eq['residuals'] for c,m in r['terms']),default=0),
        used_coordinates=sorted(used),unconstrained_coordinates=sorted(set(range(len(eq['variables'])))-used))

def projection_check(A,src,dst,c,receipt,expanded,metrics):
    need(set(c)=={'schema','input_sha256','output_sha256','steps','unconstrained_removed','retained_original_variables','retained_original_rows','metrics'} and c['schema']=='integer_quadratic_elimination_v1','whole integral monic certificate')
    need(all(type(i) is int for k in ['unconstrained_removed','retained_original_variables','retained_original_rows'] for i in c[k]),'integer coordinate/row partition metadata')
    steps=A.projection(src,dst,c)
    for q in c['steps']:
        need(set(q)=={'row_id','variable','name','kind','restoration','restoration_degree'},'whole monic step metadata')
        need(type(q['row_id']) is int and type(q['restoration_degree']) is int,'integer monic row/degree metadata')
        i=q['variable']; need(type(i) is int and 0<=i<len(src['variables']),'monic variable namespace')
        need(q['name']==src['variables'][i]['name'] and q['kind']==src['variables'][i].get('kind'),'actual monic coordinate metadata')
        need(q['restoration_degree']==A.deg(A.norm(q['restoration'])) and len(A.norm(q['restoration']))<=16,'restoration degree/support')
    poly,used=A.literal(dst); n=len(dst['variables']); r=len(dst['residuals'])
    measured={'input_variables':len(src['variables']),'output_variables':n,'input_rows':len(src['residuals']),'output_rows':r,
        'eliminated_coordinates':steps,'unconstrained_removed':len(c['unconstrained_removed']),
        'by_restoration_degree':dict(Counter(str(q['restoration_degree']) for q in c['steps'])),
        'by_kind':dict(Counter(q['kind'] for q in c['steps'])),'max_support':16,'affine_support':None,'quadratic_first':False,
        'max_output_row_terms':max((len(A.norm(q)) for q in dst['residuals']),default=0),
        'expanded_monomials':len(poly),'exact_degree':A.deg(poly),'max_abs_expanded_coefficient':max(map(abs,poly.values()),default=0),
        'max_abs_row_coefficient':max((abs(c) for row in dst['residuals'] for c,m in row['terms']),default=0)}
    need(canon(c['metrics'])==canon(measured),'every actual engine census and declared default policy')
    expected=copy.deepcopy(src); expected['variables']=dst['variables']; expected['residuals']=dst['residuals']
    expected['metrics']={'variables':n,'quadratic_rows':r,'variable_kinds':dict(Counter(v.get('kind') for v in dst['variables'])),
        **{k:measured[k] for k in ['expanded_monomials','exact_degree','max_abs_expanded_coefficient','max_abs_row_coefficient']}}
    expected['elimination']={'method':'integral monic quadratic substitution','certificate':'terminal_elimination_certificate.json'}
    need(canon(dst)==canon(expected),'entire projected metadata/header')
    need(canon(receipt)==canon(dict(status='PASS',verified_steps=steps,output_variables=n,output_rows=r)),'whole engine verification receipt')
    need(canon(expanded)==canon(dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',variables=n,terms=A.terms(poly))),'all collected SOS coefficients and header')
    need(A.deg(poly)==4 and used==set(range(n)),'actual quartic degree and retained coordinate use')
    actual=census(A,dst,poly,used); need(canon(metrics)==canon(actual),'entire published raw census')
    fixtures=[]
    for seed,free in [(7,0),(19,-5),(23,3)]:
        target=[((i*seed+3)%11)-5 for i in range(n)]
        values={i:target[j] for j,i in enumerate(c['retained_original_variables'])}
        for i in c['unconstrained_removed']: values[i]=free
        for q in reversed(c['steps']): values[q['variable']]=evaluate(A.norm(q['restoration']),values)
        need(set(values)==set(range(len(src['variables']))),'complete inverse including every actual free coordinate')
        kept={r:evaluate(A.norm(dst['residuals'][j]),dict(enumerate(target))) for j,r in enumerate(c['retained_original_rows'])}
        for i,row in enumerate(src['residuals']): need(evaluate(A.norm(row),values)==kept.get(i,0),'whole inverse residual identity '+str(i))
        fixtures.append(dict(seed=seed,free_value=free,actual_free_coordinates=c['unconstrained_removed'],rows_checked=len(src['residuals'])))
    return measured,actual,fixtures

def profile_check(A,name,d,pinhash):
    rows,ordinary=source_check(A,name,d)
    horn=horn_check(A,d['source'],d['factored_source'],d['factorization_certificate'],d['HORN_WITNESS_MAP'],rows,ordinary)
    c=d['terminal_elimination_certificate']; wm=d['HORN_WITNESS_MAP']
    engine,raw,fixtures=projection_check(A,d['factored_source'],d['projected'],c,d['ENGINE_VERIFICATION'],d['expanded_polynomial'],d['METRICS'])
    composed=dict(schema='round16_composed_integer_maps_v1',source_coordinates=len(d['source']['variables']),factored_coordinates=len(d['factored_source']['variables']),
        source_to_factored=wm['source_to_factored'],factored_to_source=wm['factored_to_source'],preserved_source_coordinates=wm['preserved_source_coordinates'],
        retained_original_variables=c['retained_original_variables'],retained_original_rows=c['retained_original_rows'],
        actual_free_factored_coordinates=c['unconstrained_removed'],reverse_monic_restorations=list(reversed(c['steps'])),
        inverse_order=['initialize_every_actual_free_factored_coordinate','reverse_all_monic_steps','overwrite_original_Horn_private_witnesses','apply_sealed_source_ordinary_maps_and_calibration'],
        forward_order=['construct_complete_sealed_source_witness','overwrite_factored_Horn_private_witnesses','retain_projected_coordinates'],
        chart='identity; no translation or centering',old_private_witness_identity_claimed=False)
    need(canon(d['COMPOSED_MAPS'])==canon(composed),'whole composed inverse/forward maps and order')
    prior={n+'.json':dict(bytes=len(canon(x)),sha256=sha(x)) for n,x in d.items() if n!='ENDPOINT_BINDING'}
    prior['source.json']=meta(SOURCE/'data'/f'{name}.json')
    expected=dict(schema='round16_raw_endpoint_binding_v1',profile=name,source_manifest_sha256=SOURCE_SEAL,source_pins_sha256=pinhash,
        all_prior_profile_files=prior,equivalence_chain=['complete_sealed_literal_source','fresh_Horn_existential_maps','fresh_integral_monic_and_free_coordinate_maps','full_literal_sum_of_squares'],
        source_restored_before_native_calibration=True,chart='raw untranslated',old_private_tuple_identity_claimed=False)
    need(canon(d['ENDPOINT_BINDING'])==canon(expected),'whole endpoint calibration and artifact binding')
    return dict(engine=engine,raw=raw,actual_free_factored_coordinates=c['unconstrained_removed']),dict(Horn=horn,signed_inverse_fixtures=fixtures)

def load(folder):
    names=['source','SOURCE_BINDING','factored_source','factorization_certificate','HORN_WITNESS_MAP','projected',
           'terminal_elimination_certificate','ENGINE_VERIFICATION','expanded_polynomial','METRICS','COMPOSED_MAPS','ENDPOINT_BINDING']
    return {n:get(folder/(n+'.json')) for n in names}

def controls(A,name,original,pinhash):
    result={}
    def corrupt_monic(d):
        q=next(q for q in d['terminal_elimination_certificate']['steps'] if q['restoration'])
        q['restoration'][0][0]+=1
    def trial(label,change):
        d=copy.deepcopy(original); change(d)
        d['factorization_certificate'].update(input_sha256=sha(d['source']),output_sha256=sha(d['factored_source']))
        d['terminal_elimination_certificate'].update(input_sha256=sha(d['factored_source']),output_sha256=sha(d['projected']))
        d['HORN_WITNESS_MAP'].update(source_sha256=sha(d['source']),factored_sha256=sha(d['factored_source']))
        try: profile_check(A,name,d,pinhash)
        except (ValueError,KeyError,IndexError,TypeError) as err: result[label]=dict(rejected=True,reason=str(err))
        else: raise ValueError('actual artifact corruption survived: '+label)
    trial('changed_Hstar_body',lambda d:d['source']['residuals'][158]['terms'][0].__setitem__(0,999))
    trial('missing_reparameterized_interval_witness_scope',lambda d:d['SOURCE_BINDING'].__setitem__('interval_triples_fresh_across_reparameterization',False))
    trial('false_Hstar_old_tuple_identity',lambda d:d['SOURCE_BINDING'].__setitem__('Hstar_H0_raw_tuple_identity',True))
    trial('wrong_native_before_source_binding',lambda d:d['SOURCE_BINDING'].__setitem__('original_compiler_or_native_program_rerun',True))
    trial('Horn_square_root_coefficient',lambda d:next(iter(d['factorization_certificate']['square_roots'].values()))[0].__setitem__(0,999))
    trial('missing_Horn_edit',lambda d:d['factorization_certificate']['changes'].pop())
    trial('wrong_Horn_deleted_definition',lambda d:d['factorization_certificate']['deleted_rows'].pop())
    trial('stale_Horn_fresh_root',lambda d:d['factorization_certificate'].__setitem__('new_root',622))
    trial('factored_Horn_coordinate_kind',lambda d:d['factored_source']['variables'][-1].__setitem__('kind','witness'))
    trial('Horn_inverse_rule',lambda d:d['HORN_WITNESS_MAP']['factored_to_source']['restorations'][0]['restoration'][0].__setitem__(0,999))
    trial('Horn_exposed_coordinate_missing',lambda d:d['HORN_WITNESS_MAP']['preserved_source_coordinates'].pop())
    trial('false_whole_old_private_bijection',lambda d:d['HORN_WITNESS_MAP'].__setitem__('full_old_private_witness_identity_claimed',True))
    trial('monic_restoration_coefficient',corrupt_monic)
    trial('monic_coordinate_name',lambda d:d['terminal_elimination_certificate']['steps'][0].__setitem__('name','forged'))
    trial('monic_restoration_degree',lambda d:d['terminal_elimination_certificate']['steps'][0].__setitem__('restoration_degree',-1))
    trial('missing_actual_free_coordinate',lambda d:d['terminal_elimination_certificate']['unconstrained_removed'].append(0))
    trial('retained_coordinate_map',lambda d:d['terminal_elimination_certificate']['retained_original_variables'].pop())
    trial('retained_row_map',lambda d:d['terminal_elimination_certificate']['retained_original_rows'].pop())
    trial('unsupported_quadratic_first_policy',lambda d:d['terminal_elimination_certificate']['metrics'].__setitem__('quadratic_first',True))
    trial('unlicensed_certificate_metadata',lambda d:d['terminal_elimination_certificate'].__setitem__('old324_step_reused',True))
    trial('wrong_engine_receipt',lambda d:d['ENGINE_VERIFICATION'].__setitem__('verified_steps',-1))
    trial('projected_row_coefficient',lambda d:d['projected']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('projected_coordinate_kind',lambda d:d['projected']['variables'][0].__setitem__('kind','forged'))
    trial('projected_header',lambda d:d['projected']['elimination'].__setitem__('certificate','forged'))
    trial('whole_quartic_coefficient',lambda d:d['expanded_polynomial']['terms'][0].__setitem__(0,d['expanded_polynomial']['terms'][0][0]+1))
    trial('whole_quartic_domain',lambda d:d['expanded_polynomial'].__setitem__('domain','nonnegative integers'))
    trial('whole_quartic_variable_census',lambda d:d['expanded_polynomial'].__setitem__('variables',-1))
    trial('published_height',lambda d:d['METRICS'].__setitem__('height',-1))
    trial('composed_free_coordinates',lambda d:d['COMPOSED_MAPS']['actual_free_factored_coordinates'].append(0))
    trial('wrong_Horn_inverse_order',lambda d:d['COMPOSED_MAPS']['inverse_order'].reverse())
    trial('endpoint_ordinary_scope',lambda d:d['ENDPOINT_BINDING'].__setitem__('source_restored_before_native_calibration',False))
    trial('missing_whole_quartic_binding',lambda d:d['ENDPOINT_BINDING']['all_prior_profile_files'].pop('expanded_polynomial.json'))
    # Exercise privacy and stale source formulas directly, beyond outer hashes.
    escaped=copy.deepcopy(original['source']); sq=original['factorization_certificate']['square_variables'][0]
    escaped['residuals'].append(dict(label='probe.private_escape',terms=[[1,[sq]]]))
    fc=copy.deepcopy(original['factorization_certificate']); fc['input_sha256']=sha(escaped)
    try: A.factorization(escaped,original['factored_source'],fc)
    except ValueError as err:
        need('signed factor escapes' in str(err),'privacy control must reach the actual escape check')
        result['actual_Horn_private_escape']=dict(rejected=True,reason=str(err))
    else: raise ValueError('private Horn escape survived')
    factored=original['factored_source']; pc=copy.deepcopy(original['terminal_elimination_certificate'])
    hstarrow=158-2
    pc['steps'].insert(0,dict(row_id=hstarrow,variable=175,name=factored['variables'][175]['name'],kind=factored['variables'][175]['kind'],restoration=[[1,[26,26]]],restoration_degree=2))
    try: A.projection(factored,original['projected'],pc)
    except ValueError as err:
        need(str(err)=='projection equation mismatch','stale175 control must reach the actual defining equation')
        result['stale_private175_equals_Nsquare']=dict(rejected=True,reason=str(err))
    else: raise ValueError('old private175 restoration survived')
    if name=='weighted':
        pc=copy.deepcopy(original['terminal_elimination_certificate']); first=[]
        for i,restore in [(140,A.add(A.v(144),A.v(145))),(144,A.mul(A.add(A.v(142),A.con(1)),A.v(143)))]:
            hits=[r for r,row in enumerate(factored['residuals']) if A.norm(row).get((i,)) in [-1,1]
                  and not any(i in m for m in A.norm(row) if m!=(i,)) and A.solved(A.norm(row),i)==restore]
            need(len(hits)==1,'actual unsafe weighted-pair definition')
            first.append(dict(row_id=hits[0],variable=i,name=factored['variables'][i]['name'],kind=factored['variables'][i]['kind'],restoration=A.terms(restore),restoration_degree=A.deg(restore)))
        pc['steps']=first+pc['steps']
        try: A.projection(factored,original['projected'],pc)
        except ValueError as err:
            need(str(err)=='projection degree increased','weighted control must reach the actual cubic row')
            result['actual_unsafe_EB_double_substitution']=dict(rejected=True,reason=str(err))
        else: raise ValueError('cubic weighted-pair substitution survived')
    poly,_=A.literal(original['projected']); positive=[]
    for label,change in [('term_permutation',lambda r:r['terms'].reverse()),('canceling_zero_pair',lambda r:r['terms'].extend([[7,[]],[-7,[]]]))]:
        eq=copy.deepcopy(original['projected']); change(eq['residuals'][0]); changed,_=A.literal(eq)
        need(changed==poly,'valid semantic polynomial control')
        positive.append(label+'; canonical literal format is checked separately')
    return dict(negative=result,positive=positive)

def output_safe(p):
    need(not any(q.is_symlink() for q in [p.absolute(),*p.absolute().parents]),'no symlink receipt path')
    target=p.resolve(); pins=get(HERE/'SOURCE_PINS.json')
    need(not any(target.is_relative_to((ROOT/n).resolve()) for n in pins['closed_dependencies']),'never write sealed parents')
    need(target not in {(ROOT/n).resolve() for n in pins['files']},'never overwrite a pinned external file')
    need(not target.is_relative_to(HERE/'vendor') and not target.is_relative_to(HERE/'data'),'receipt outside reviewed/generated inputs')
    need(target not in {HERE/n for n in list(pins['core'])+['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json']},'never overwrite author inputs')
    need(not (HERE/'MANIFEST.json').exists() or not target.is_relative_to(HERE),'receipt outside sealed packet')

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--data',type=Path,default=HERE/'data'); p.add_argument('--output',type=Path,required=True)
    a=p.parse_args(); pinhash=authenticate(); output_safe(a.output); A=support(); index=get(a.data/'INDEX.json')
    need((a.data/'INDEX.json').read_bytes()==canon(index),'canonical whole generated index')
    need(set(index)=={'schema','source_pins_sha256','producer_sha256','policy','summary','files'} and index['schema']=='round16_two_raw_projection_inventory_v1','entire generated index header')
    need(index['source_pins_sha256']==pinhash and index['producer_sha256']==meta(HERE/'build.py')['sha256'] and canon(index['policy'])==canon(POLICY),'whole index source/producer/policy binding')
    names=['source','SOURCE_BINDING','factored_source','factorization_certificate','HORN_WITNESS_MAP','projected','terminal_elimination_certificate','ENGINE_VERIFICATION','expanded_polynomial','METRICS','COMPOSED_MAPS','ENDPOINT_BINDING']
    need(set(index['files'])=={profile+'/'+n+'.json' for profile in PROFILES for n in names} and index['files']==inventory(a.data),'every actual generated artifact byte')
    profiles={}; details={}; mutations={}
    for name in PROFILES:
        for n in names:
            path=a.data/name/(n+'.json')
            need(path.read_bytes()==((SOURCE/'data'/f'{name}.json').read_bytes() if n=='source' else canon(get(path))),'whole literal serialization '+name+'/'+n)
        d=load(a.data/name); profiles[name],details[name]=profile_check(A,name,d,pinhash); mutations[name]=controls(A,name,d,pinhash)
    need(canon(index['summary'])==canon(profiles),'every actual summary measurement')
    record=dict(status='PASS',optimized_python=bool(sys.flags.optimize),checker_sha256=meta(HERE/'check.py')['sha256'],source_pins_sha256=pinhash,
        index_sha256=sha(index),profiles=profiles,independent_maps=details,actual_controls=mutations,
        scope='Whole raw quadratic/SOS artifacts and integral Horn/monic existence maps at the exact sealed source; no private tuple identity, translation or optimality claim.')
    out=(json.dumps(record,indent=2,sort_keys=True)+'\n').encode(); need(not a.output.exists() or a.output.read_bytes()==out,'refuse changed receipt overwrite')
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_bytes(out); print(out.decode(),end='')
if __name__=='__main__': main()
