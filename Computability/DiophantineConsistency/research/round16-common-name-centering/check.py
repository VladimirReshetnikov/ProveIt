#!/usr/bin/env python3
"""Independent fixed58 translation verifier. CODE ONLY/HOLD for full review."""
import argparse, copy, hashlib, importlib.util, json, sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
RAW=ROOT/'research/round16-square-weighted-projections'
PLAN=ROOT/'research/round16-common-name-centering-plan'
OLD=ROOT/'research/signed-pell-cap-nine-factor-projections'
SEALS={'research/round16-square-weighted-projections':'34b2b1b6f27dea48cfc7692ad64e5a034304e76cb0d3ef47eae87ec194862acd',
       'research/round16-common-name-centering-plan':'ed0f0365d85209797f50fd450bde8b929fc853772e9ae2fb1d1346d090bff4e1',
       'research/signed-pell-cap-nine-factor-projections':'c48ecc2d0cf12e125ecc9ab45849073e6d06a303a38e130aa6fd42859168aefd'}
PROFILES=['plain','weighted']
NAMES=['equation','expanded_polynomial','translation_certificate','METRICS','COMPOSED_MAPS','ENDPOINT_BINDING']
POLICY=dict(name='fixed58_common_names',profiles=PROFILES,shifts_per_profile=58,
            search=False,optional_initial_recipe=False,raw_coordinates_preserved=True)

def need(ok,why):
    if not ok: raise ValueError(why)
def get(p): return json.loads(p.read_bytes())
def canon(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b): return hashlib.sha256(b).hexdigest()
def sha(x): return digest(canon(x))
def object_meta(x):
    b=canon(x); return dict(bytes=len(b),sha256=digest(b))
def meta(p):
    b=p.read_bytes(); return dict(bytes=len(b),sha256=digest(b))
def inventory(p,skip='INDEX.json'):
    return {str(q.relative_to(p)):meta(q) for q in sorted(p.rglob('*')) if q.is_file() and q!=p/skip}

def authenticate():
    pins=get(HERE/'SOURCE_PINS.json'); need(pins['closed_dependencies']==SEALS,'exact three sealed parents')
    for n,m in pins['files'].items(): need(meta(ROOT/n)==m,'external '+n)
    for n,m in pins['core'].items(): need(meta(HERE/n)==m,'reviewed core '+n)
    for n,m in pins['vendor'].items(): need(meta(HERE/'vendor'/n)==m,'reviewed vendor '+n)
    for n,s in SEALS.items():
        p=ROOT/n; need(meta(p/'MANIFEST.json')['sha256']==s,'parent seal '+n)
        d=get(p/'MANIFEST.json')['files']; a=inventory(p,'MANIFEST.json')
        need(d=={k:v if isinstance(d.get(k),dict) else v['sha256'] for k,v in a.items()},'whole parent inventory '+n)
    need(all(meta(HERE/n)==m for n,m in get(HERE/'HOLD_INVENTORY.json')['files'].items()),'all original held bytes')
    if (HERE/'MANIFEST.json').exists():
        need(get(HERE/'MANIFEST.json')['files']==inventory(HERE,'MANIFEST.json'),'whole final author inventory')
    return meta(HERE/'SOURCE_PINS.json')['sha256']

def safe_receipt(path,data):
    path=path.absolute(); need(not any(q.is_symlink() for q in [path,*path.parents]),'no symlink receipt path')
    target=path.resolve(); pins=get(HERE/'SOURCE_PINS.json')
    need(not any(target.is_relative_to((ROOT/n).resolve()) for n in SEALS),'never write sealed parents')
    need(target not in {(ROOT/n).resolve() for n in pins['files']},'never overwrite pinned input')
    need(not target.is_relative_to(HERE/'vendor'),'never write vendor')
    need(target not in {HERE/n for n in list(pins['core'])+['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json']},'never write reviewed core')
    need(not target.is_relative_to(data.resolve()),'receipt outside selected data')
    need(not (HERE/'MANIFEST.json').exists() or not target.is_relative_to(HERE),'receipt outside sealed packet')

def support():
    # Sole nonstdlib import, after all adopted bytes and parent inventories authenticate.
    spec=importlib.util.spec_from_file_location('independent_translation_algebra',HERE/'vendor/check_direct.py')
    A=importlib.util.module_from_spec(spec); spec.loader.exec_module(A); return A

def derive_policy():
    old=get(OLD/'data/projected.json'); cert=get(OLD/'data/centered/translation_certificate.json')
    names={}
    for p in PROFILES:
        vs=get(RAW/'data'/p/'projected.json')['variables']; names[p]={v['name']:i for i,v in enumerate(vs)}
        need(len(names[p])==len(vs),'unique complete raw names')
    need(len(cert['shifts'])==61 and len({i for i,s in cert['shifts']})==61,'complete old61 shift table')
    common=[]; absent=[]
    for i,s in cert['shifts']:
        need(type(i) is int and type(s) is int and s!=0 and 0<=i<len(old['variables']),'old final integer shift')
        n=old['variables'][i]['name']
        q=dict(literal_name=n,old_index=i,shift=s,plain_index=names['plain'].get(n),weighted_index=names['weighted'].get(n))
        (common if all(q[p+'_index'] is not None for p in PROFILES) else absent).append(q)
    need(len(common)==58 and len(absent)==3,'exact common58/absent3 recipe')
    plan=get(PLAN/'SOURCE_PINS.json')['policy']
    need(plan==dict(name='inherited_final_centered_shifts_at_exact_common_names',
        convention='raw_coordinate = chart_coordinate + shift',inverse='chart_coordinate = raw_coordinate - shift',
        all_other_shifts=0,perform_search=False,inherit_old_search_history_or_scores=False,
        shifts=common,absent_old_nonzero_shifts=absent),'complete accepted plan policy')
    return dict(name=POLICY['name'],plan_manifest_sha256=SEALS[str(PLAN.relative_to(ROOT))],
        old_recipe_manifest_sha256=SEALS[str(OLD.relative_to(ROOT))],
        old_recipe_certificate=meta(OLD/'data/centered/translation_certificate.json'),
        name_index_association=common,absent_old_nonzero_shifts=absent,all_other_shifts=0,search=False)

def expected_maps(name,raw,chart,cert):
    parent=get(RAW/'data'/name/'COMPOSED_MAPS.json')
    return dict(schema='round16_translated_composed_integer_maps_v1',profile=name,
        raw_parent_manifest_sha256=SEALS[str(RAW.relative_to(ROOT))],raw_projected_sha256=sha(raw),chart_sha256=sha(chart),
        translation=dict(shifts=cert['shifts'],raw_to_chart='z_i = x_i - delta_i',chart_to_raw='x_i = z_i + delta_i'),
        all_raw_coordinates_retained=True,parent_maps=parent,source_binding=get(RAW/'data'/name/'SOURCE_BINDING.json'),
        raw_endpoint_binding=get(RAW/'data'/name/'ENDPOINT_BINDING.json'),
        inverse_order=['add_fixed_delta_to_recover_raw_projected_tuple']+parent['inverse_order'],
        forward_order=parent['forward_order']+['subtract_fixed_delta_from_raw_projected_tuple'],
        no_old_private_tuple_identity=True,original_native_or_source_program_rerun=False)

def expected_endpoint(name,d,pinhash):
    return dict(schema='round16_fixed_translation_endpoint_v1',profile=name,source_pins_sha256=pinhash,
        raw_parent_manifest_sha256=SEALS[str(RAW.relative_to(ROOT))],raw_data_index=meta(RAW/'data/INDEX.json'),
        all_prior_profile_files={n+'.json':object_meta(d[n]) for n in NAMES if n!='ENDPOINT_BINDING'},
        equivalence_chain=['fixed_integer_translation_bijection','complete_accepted_raw_projection_and_Horn_maps','whole_sealed_source_ordinary_calibration'],
        inverse_translation_before_raw_witness_maps=True,old327_polynomial_identity_claimed=False,search_or_optimality_claimed=False)

def evaluate(poly,values):
    out=0
    for mon,c in poly.items():
        term=c
        for i in mon: term*=values[i]
        out+=term
    return out

def verify(A,name,d,pinhash,policy):
    raw=get(RAW/'data'/name/'projected.json'); eq=d['equation']; cert=d['translation_certificate']
    pairs=sorted([[q[name+'_index'],q['shift']] for q in policy['name_index_association']])
    need(set(cert)=={'schema','profile','input_sha256','output_sha256','convention','inverse','shifts','fixed_policy'},'exact certificate fields; no search history')
    need(cert['schema']=='integral_translation_v1' and cert['profile']==name,'certificate schema/profile')
    need(cert['convention']=='old_coordinate = new_coordinate + shift' and cert['inverse']=='new_coordinate = old_coordinate - shift','exact inverse convention')
    need(all(isinstance(q,list) and len(q)==2 and type(q[0]) is int and type(q[1]) is int and q[1]!=0 for q in cert['shifts']),'strict integer shift records')
    need(cert['shifts']==pairs and len(pairs)==58 and len({i for i,s in pairs})==58,'exact58 sorted shifts')
    need(canon(cert['fixed_policy'])==canon(policy),'whole independent name/index policy')
    need(cert['input_sha256']==sha(raw) and cert['output_sha256']==sha(eq),'whole translation hash binding')
    need(raw['domain']=='unrestricted integers','raw integer domain')
    header={k:copy.deepcopy(v) for k,v in raw.items() if k not in {'residuals','metrics','elimination'}}
    header['variant']+=':integral_translation'
    need(canon(header)==canon({k:v for k,v in eq.items() if k!='residuals'}),'literal translation mismatch: exact equation metadata')
    need(A.translation(raw,eq,cert)==58,'whole adopted translation replay')
    need(all(canon({k:v for k,v in r.items() if k!='terms'})==canon({k:v for k,v in t.items() if k!='terms'}) for r,t in zip(raw['residuals'],eq['residuals'])),'literal translation mismatch: exact row metadata')
    need(canon(d['COMPOSED_MAPS'])==canon(expected_maps(name,raw,eq,cert)),'whole composed inverse and source calibration')
    parent=d['COMPOSED_MAPS']['parent_maps']; pc=get(RAW/'data'/name/'terminal_elimination_certificate.json')
    need(parent['retained_original_variables']==pc['retained_original_variables'] and
         parent['actual_free_factored_coordinates']==pc['unconstrained_removed'] and
         parent['reverse_monic_restorations']==list(reversed(pc['steps'])),'actual complete monic/free interface')
    need(len(pc['unconstrained_removed'])==83 and len(pc['steps'])=={'plain':204,'weighted':203}[name],'accepted actual83/free monic cardinalities')
    rawpoly,rawused=A.literal(raw); poly,used=A.literal(eq)
    rp=get(RAW/'data'/name/'expanded_polynomial.json'); out=d['expanded_polynomial']
    need(set(rp)==set(out)=={'schema','domain','variables','terms'},'whole expanded polynomial fields')
    header=dict(schema='sparse_integer_polynomial_v1',domain=raw['domain'],variables=len(raw['variables']))
    need(canon({k:rp[k] for k in header})==canon(header) and canon({k:out[k] for k in header})==canon(header),'whole polynomial header')
    need(A.norm(rp)==rawpoly and A.norm(out)==poly,'every raw/chart SOS coefficient')
    n=len(eq['variables']); need(used==rawused==set(range(n)),'all retained coordinates live')
    need(A.deg(poly)==A.deg(rawpoly)==4,'exact complete quartic degree')
    metrics=dict(variables=n,rows=len(eq['residuals']),degree=A.deg(poly),monomials=len(poly),
        height=max(map(abs,poly.values())),row_height=max(abs(c) for r in eq['residuals'] for c in A.norm(r).values()),
        used_coordinates=sorted(used),unconstrained_coordinates=[])
    need(canon(d['METRICS'])==canon(metrics),'whole independently recollected census')
    need(canon(d['ENDPOINT_BINDING'])==canon(expected_endpoint(name,d,pinhash)),'complete new endpoint binding')
    reverse=poly
    for i,s in pairs: reverse=A.sub(reverse,i,A.add(A.v(i),A.con(-s)))
    need(reverse==rawpoly,'reverse every whole quartic coefficient')
    need({m:c for m,c in poly.items() if len(m)==4}=={m:c for m,c in rawpoly.items() if len(m)==4},'entire leading homogeneous form')
    shifts=dict(pairs)
    for seed in [-2,3]:
        z=[(i*seed)%7-3 for i in range(n)]; x=[v+shifts.get(i,0) for i,v in enumerate(z)]
        need([x[i]-shifts.get(i,0) for i in range(n)]==z,'full integer coordinate inverse')
        need(all(evaluate(A.norm(r),x)==evaluate(A.norm(t),z) for r,t in zip(raw['residuals'],eq['residuals'])),'every residual signed translation fixture')
        need(evaluate(rawpoly,x)==evaluate(poly,z),'whole SOS signed translation fixture')
    return metrics

def controls(A,name,base,pinhash,policy):
    trials=[]
    def add(label,change,error): trials.append((label,change,error))
    def cert(d): return d['translation_certificate']
    def replace_poly(d,mon):
        p=A.norm(d['expanded_polynomial']); p[mon]=p.get(mon,0)+1; d['expanded_polynomial']['terms']=A.terms(p)
    add('wrong_shift_sign',lambda d:cert(d)['shifts'][0].__setitem__(1,-cert(d)['shifts'][0][1]),'exact58 sorted shifts')
    add('duplicate_shift',lambda d:cert(d)['shifts'].__setitem__(1,cert(d)['shifts'][0]),'exact58 sorted shifts')
    add('missing_shift',lambda d:cert(d)['shifts'].pop(),'exact58 sorted shifts')
    add('boolean_index',lambda d:cert(d)['shifts'][0].__setitem__(0,False),'strict integer shift')
    add('float_shift',lambda d:cert(d)['shifts'][0].__setitem__(1,-17.0),'strict integer shift')
    add('wrong_name',lambda d:cert(d)['fixed_policy']['name_index_association'][0].__setitem__('literal_name','not_t0'),'name/index policy')
    add('wrong_name_index',lambda d:cert(d)['fixed_policy']['name_index_association'][0].__setitem__(name+'_index',1),'name/index policy')
    add('wrong_schema',lambda d:cert(d).__setitem__('schema','old_recipe'),'schema/profile')
    add('wrong_convention',lambda d:cert(d).__setitem__('convention','old=new-shift'),'inverse convention')
    add('wrong_inverse',lambda d:cert(d).__setitem__('inverse','new=old+shift'),'inverse convention')
    add('old_search_history',lambda d:cert(d).__setitem__('search_history',[]),'certificate fields')
    add('old_score',lambda d:cert(d).__setitem__('score',[128446,5718]),'certificate fields')
    add('stale_input_hash',lambda d:cert(d).__setitem__('input_sha256','0'*64),'translation hash')
    add('changed_row_constant',lambda d:d['equation']['residuals'][0]['terms'].append([1,[]]),'literal translation mismatch')
    add('missing_body_row',lambda d:d['equation']['residuals'].pop(),'literal translation mismatch')
    add('changed_variable_name',lambda d:d['equation']['variables'][0].__setitem__('name','wrong_t0'),'literal translation mismatch')
    add('changed_row_label',lambda d:d['equation']['residuals'][0].__setitem__('label','wrong_label'),'literal translation mismatch')
    add('wrong_domain',lambda d:d['equation'].__setitem__('domain','naturals'),'literal translation mismatch')
    add('stale_cached_metrics',lambda d:d['equation'].__setitem__('metrics',{}),'literal translation mismatch')
    add('wrong_variant_suffix',lambda d:d['equation'].__setitem__('variant',d['equation']['variant']+':finite_centering'),'literal translation mismatch')
    add('constant_coefficient',lambda d:replace_poly(d,()),'SOS coefficient')
    mixed=next(m for m in A.norm(base['expanded_polynomial']) if len(set(m))>=2)
    add('mixed_coefficient',lambda d:replace_poly(d,mixed),'SOS coefficient')
    add('missing_polynomial_term',lambda d:d['expanded_polynomial']['terms'].pop(),'SOS coefficient')
    add('wrong_polynomial_header',lambda d:d['expanded_polynomial'].__setitem__('variables',1),'polynomial header')
    add('wrong_height',lambda d:d['METRICS'].__setitem__('height',1),'recollected census')
    add('wrong_row_census',lambda d:d['METRICS'].__setitem__('rows',1),'recollected census')
    add('stale_free_map',lambda d:d['COMPOSED_MAPS']['parent_maps']['actual_free_factored_coordinates'].pop(),'composed inverse')
    add('stale_monic_map',lambda d:d['COMPOSED_MAPS']['parent_maps']['reverse_monic_restorations'].pop(),'composed inverse')
    add('wrong_inverse_order',lambda d:d['COMPOSED_MAPS']['inverse_order'].reverse(),'composed inverse')
    add('wrong_chart_inverse_sign',lambda d:d['COMPOSED_MAPS']['translation'].__setitem__('chart_to_raw','x=z-delta'),'composed inverse')
    add('stale_source_calibration',lambda d:d['COMPOSED_MAPS']['source_binding'].__setitem__('original_compiler_or_native_program_rerun',True),'composed inverse')
    add('wrong_endpoint_parent',lambda d:d['ENDPOINT_BINDING'].__setitem__('raw_parent_manifest_sha256','0'*64),'endpoint binding')
    rejected=[]
    for label,change,error in trials:
        d=copy.deepcopy(base); change(d)
        # Rebind the changed equation's inner output hash, not just the outer file inventory.
        cert(d)['output_sha256']=sha(d['equation'])
        try: verify(A,name,d,pinhash,policy)
        except ValueError as e:
            need(error in str(e),'intended semantic rejection '+label+': '+str(e)); rejected.append(label)
        else: raise ValueError('accepted actual artifact mutation '+label)
    positive=[]
    for label in ['reordered_terms','canceling_terms']:
        d=copy.deepcopy(base)
        if label=='reordered_terms': d['expanded_polynomial']['terms'].reverse()
        else: d['expanded_polynomial']['terms'] += [[7,[0,1]],[-7,[0,1]]]
        d['ENDPOINT_BINDING']=expected_endpoint(name,d,pinhash)
        verify(A,name,d,pinhash,policy); positive.append(label)
    return dict(rejected_actual_artifacts=rejected,accepted_algebraic_controls=positive)

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--data',type=Path,default=HERE/'data')
    p.add_argument('--output',type=Path,required=True); a=p.parse_args()
    pinhash=authenticate(); safe_receipt(a.output,a.data); A=support(); policy=derive_policy()
    index=get(a.data/'INDEX.json'); files=inventory(a.data)
    need(set(files)=={p+'/'+n+'.json' for p in PROFILES for n in NAMES},'exact twelve generated payloads')
    need(index['files']==files,'whole data file inventory')
    for q in a.data.rglob('*'):
        if q.is_file(): need(q.read_bytes()==canon(get(q)),'canonical generated JSON '+str(q))
    summary={}; evidence={}
    for name in PROFILES:
        d={n:get(a.data/name/(n+'.json')) for n in NAMES}
        summary[name]=verify(A,name,d,pinhash,policy); evidence[name]=controls(A,name,d,pinhash,policy)
    expected=dict(schema='round16_fixed_two_chart_inventory_v1',source_pins_sha256=pinhash,
        producer_sha256=meta(HERE/'build.py')['sha256'],policy=POLICY,summary=summary,files=files)
    need(canon(index)==canon(expected),'whole independent index metadata')
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_pins_sha256=pinhash,
        index_sha256=sha(index),summary=summary,controls=evidence,
        exact_shifts_per_profile=58,full_quartic_reverse_substitution=True,signed_fixtures_per_profile=2,
        scope='Complete fixed translations and accepted raw source maps; no source/native program, optimizer, search or global optimum replay.')
    out=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
    need(not a.output.exists() or a.output.read_bytes()==out,'refuse changed receipt overwrite')
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_bytes(out); print(out.decode(),end='')
if __name__=='__main__': main()
