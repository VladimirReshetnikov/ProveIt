#!/usr/bin/env python3
"""Optimizer-free coefficient/certificate verifier. Execution is under review."""
import argparse, copy, hashlib, importlib.util, json, sys
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'
VARIANTS={'F_only':[2],'joint_F_A':[2,25]}
sys.dont_write_bytecode=True

def need(ok,msg):
    if not ok:raise ValueError(msg)
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(x):return digest(canon(x))
def get(p):return json.loads(p.read_bytes())
def files(p,skip):return {str(q.relative_to(p)):digest(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and str(q.relative_to(p))!=skip}
def closed(p):
    if not (p/'MANIFEST.json').exists():return
    m=get(p/'MANIFEST.json');need(files(p,'MANIFEST.json')==m['files'],'closed manifest '+str(p))
def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'source pin '+n)
    for n,h in pins['vendor'].items():need(digest((HERE/'vendor'/n).read_bytes())==h,'vendor pin '+n)
    for n,h in pins['core'].items():need(digest((HERE/n).read_bytes())==h,'core pin '+n)
    for n,h in pins['closed_dependencies'].items():
        need(digest((ROOT/n/'MANIFEST.json').read_bytes())==h,'dependency manifest pin '+n);closed(ROOT/n)
    closed(HERE)
    return digest((HERE/'SOURCE_PINS.json').read_bytes())

def independent_support():
    # Exact accepted verifier, standard library only. No E/S/F/T or builder import.
    spec=importlib.util.spec_from_file_location('round15_independent_support',HERE/'vendor/check_direct.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def parents(A):
    s=get(PARENT/'source.json');g=get(PARENT/'guarded.json');c=get(PARENT/'transform_certificate.json');p=get(PARENT/'pruning_certificate.json')
    n=len(s['variables']);r=len(s['residuals']);need((n,r,len(c['guards']))==(522,446,38),'accepted source census')
    e=copy.deepcopy(s)
    seen=set()
    for j,q in enumerate(c['guards']):
        aa=list(range(n+3*j,n+3*j+3));need(q['auxiliary']==aa and q['row']==r+j,'original guard order')
        if q['kind']=='nonnegative':expr=A.v(q['coordinate'])
        elif q['kind']=='positive_common_V':expr=A.add(A.v(251),A.con(-1))
        else:need(q['kind']=='paired_interval','guard kind');expr=A.mul(A.v(q['pair'][0]),A.v(q['pair'][1]))
        need(A.norm(q['expression'])==expr,'original guard expression')
        a,b,d=aa;row={'label':'domain_guard.'+str(j),'terms':A.terms(A.add(expr,{(a,a):-1,(b,b):-1,(d,d):-1,(d,):-1}))}
        e['variables'] += [{'name':'guard'+str(j)+'.'+x,'kind':'integer_guard'} for x in ['a','b','c']]
        e['residuals'].append(row)
        for v in aa:
            hits=[i for i,x in enumerate(g['residuals']) if any(v in m for m in A.norm(x))]
            need(hits==[r+j] and v not in seen,'original guard privacy');seen.add(v)
    need(e==g and seen==set(range(n,len(g['variables']))),'entire original guarded parent')
    for j,v in [(2,3),(25,246)]:need(c['guards'][j]['kind']=='nonnegative' and c['guards'][j]['coordinate']==v,'omitted sign identity')
    return s,g,c,p

def source_check(A,name,d,base):
    s,g,c,oldp=base;omit=VARIANTS[name];m=d['GUARD_MAP'];z=d['guarded']
    rv=sorted(a for j in omit for a in c['guards'][j]['auxiliary']);rr=sorted(c['guards'][j]['row'] for j in omit)
    kv=[i for i in range(len(g['variables'])) if i not in rv];kr=[i for i in range(len(g['residuals'])) if i not in rr]
    vm={v:i for i,v in enumerate(kv)};rm={r:i for i,r in enumerate(kr)}
    def rt(ts):return [[co,[vm[i] for i in mon]] for co,mon in ts]
    expected=copy.deepcopy(g);expected['variables']=[g['variables'][i] for i in kv]
    expected['residuals']=[dict(g['residuals'][i],terms=rt(g['residuals'][i]['terms'])) for i in kr]
    need(z==expected,'complete compact guarded source')
    need(z['variables'][:522]==s['variables'] and z['residuals'][:446]==s['residuals'],'complete fixed body')
    gs=[]
    for j,q in enumerate(c['guards']):
        if j in omit:continue
        nq=copy.deepcopy(q);nq['expression']=rt(q['expression']);nq['auxiliary']=[vm[x] for x in q['auxiliary']];nq['row']=rm[q['row']]
        gs.append({'original_guard':j,'old':q,'new':nq})
        for a in nq['auxiliary']:
            need([i for i,row in enumerate(z['residuals']) if any(a in mon for mon in A.norm(row))]==[nq['row']],'compacted guard privacy')
    expected_map={'schema':'round15_guard_filter_v1','variant':name,'input_sha256':sha(g),'body_sha256':sha(s),'output_sha256':sha(z),
        'omitted_guards':[{'original_guard':j,'guard':c['guards'][j]} for j in omit], 'removed_variables':rv,'removed_rows':rr,
        'retained_variables':[[v,vm[v]] for v in kv],'retained_rows':[[r,rm[r]] for r in kr],
        'body_coordinates':list(range(522)),'body_rows':list(range(446)),'retained_guards':gs,
        'witness_map':'Retain and rename remaining auxiliary triples; omitted signs use the separately sealed ordinary theorem and fresh Legendre triples.'}
    need(m==expected_map,'full guard map and omission boundary')
    drop=[{'row':rm[q['row']],'variable':vm[q['variable']],'restoration':rt(q['restoration'])} for q in oldp['dropped_private_slacks']]
    need(d['pruning_certificate']['dropped_private_slacks']==drop and len(drop)==13,'old pruning transported through compaction')
    A.pruning(z,d['pruned_source'],d['pruning_certificate'],c['seeds'])
    A.literal(z);A.literal(d['pruned_source'])
    return {'guards':len(gs),'guarded_variables':len(z['variables']),'guarded_rows':len(z['residuals']),
        'body_coordinates':522,'body_rows':446,'private_slacks':len(drop),'guard_map_sha256':sha(m)}

def census(A,e,p):
    return {'variables':len(e['variables']),'rows':len(e['residuals']),'degree':A.deg(p),'monomials':len(p),
        'height':max(map(abs,p.values()),default=0),'row_height':max((abs(c) for row in e['residuals'] for c,m in row['terms']),default=0)}

def projection_metadata(A,src,dst,c,receipt):
    need(c['schema']=='integer_quadratic_elimination_v1','projection schema')
    for q in c['steps']:
        i=q['variable'];need(type(i) is int and 0<=i<len(src['variables']),'step variable')
        need(q['name']==src['variables'][i]['name'] and q['kind']==src['variables'][i].get('kind'),'step coordinate metadata')
        need(q['restoration_degree']==A.deg(A.norm(q['restoration'])) and len(A.norm(q['restoration']))<=16,'step degree/support metadata')
    poly,used=A.literal(dst);steps=c['steps'];n=len(dst['variables']);r=len(dst['residuals'])
    metrics={'input_variables':len(src['variables']),'output_variables':n,'input_rows':len(src['residuals']),'output_rows':r,
        'eliminated_coordinates':len(steps),'unconstrained_removed':len(c['unconstrained_removed']),
        'by_restoration_degree':dict(Counter(str(q['restoration_degree']) for q in steps)),
        'by_kind':dict(Counter(q['kind'] for q in steps)),'max_support':16,'affine_support':None,'quadratic_first':False,
        'max_output_row_terms':max((len(A.norm(q)) for q in dst['residuals']),default=0),
        'expanded_monomials':len(poly),'exact_degree':A.deg(poly),'max_abs_expanded_coefficient':max(map(abs,poly.values()),default=0),
        'max_abs_row_coefficient':max((abs(c) for row in dst['residuals'] for c,m in row['terms']),default=0)}
    need(c['metrics']==metrics,'all engine statistics')
    e=copy.deepcopy(src);e['variables']=dst['variables'];e['residuals']=dst['residuals']
    e['metrics']={'variables':n,'quadratic_rows':r,'variable_kinds':dict(Counter(v.get('kind') for v in e['variables'])),
        **{k:metrics[k] for k in ['expanded_monomials','exact_degree','max_abs_expanded_coefficient','max_abs_row_coefficient']}}
    e['elimination']={'method':'integral monic quadratic substitution','certificate':'terminal_elimination_certificate.json'}
    need(e==dst,'entire projected equation metadata')
    need(receipt=={'status':'PASS','verified_steps':len(steps),'output_variables':n,'output_rows':r},'engine verification record')
    need(used==set(range(n)),'projected retained coordinates actually used')
    return metrics

def evaluate(p,values):
    total=0
    for mon,c in p.items():
        val=c
        for i in mon:val*=values[i]
        total+=val
    return total

def inverse_fixtures(A,src,dst,c):
    records=[]
    for seed in [7,19]:
        target=[((i*seed+3)%11)-5 for i in range(len(dst['variables']))]
        old={i:target[j] for j,i in enumerate(c['retained_original_variables'])}
        for i in c['unconstrained_removed']:old[i]=0
        for q in reversed(c['steps']):old[q['variable']]=evaluate(A.norm(q['restoration']),old)
        need(set(old)==set(range(len(src['variables']))),'whole inverse fixture coordinate coverage')
        surviving={r:evaluate(A.norm(dst['residuals'][j]),dict(enumerate(target))) for j,r in enumerate(c['retained_original_rows'])}
        for i,row in enumerate(src['residuals']):need(evaluate(A.norm(row),old)==surviving.get(i,0),'signed inverse fixture row '+str(i))
        records.append({'seed':seed,'coordinates_restored':len(old),'rows_checked':len(src['residuals'])})
    return records

def chart_check(A,projected,plain,name,d):
    e=d['equation'];tc=d['translation_certificate'];A.translation(projected,e,tc)
    need(tc['schema']=='integral_translation_v1' and tc['convention']=='old=new+shift','translation convention')
    shifts=dict(tc['shifts']);need(all(type(i) is int for i in shifts),'translation index type')
    if name=='plain':
        expected={i:(-16 if v['name']=='t0' else -1) for i,v in enumerate(projected['variables'])
            if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
        need(tc=={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(e),
            'shifts':[[i,s] for i,s in expected.items()],'convention':'old=new+shift'},'exact original translation policy')
    else:
        need(tc['source_translation_sha256']==sha(plain['translation_certificate']),'centering translation parent')
        running=dict(plain['translation_certificate']['shifts']);history=tc['search_history']
        need(tc['search_scope']=='Eight coordinate-descent passes over non-guard coordinates, local increments ±1,±2,±3,±4,±8; no global optimality claim.','centering scope')
        previous=(-1,-1);running_rows=[A.norm(r) for r in plain['equation']['residuals']]
        def score(rows):
            poly={}
            for row in rows:poly=A.add(poly,A.mul(row,row))
            return [max(map(abs,poly.values()),default=0),len(poly),sum(map(abs,poly.values()))]
        previous_score=score(running_rows)
        for q in history:
            stage,i,delta=q['pass'],q['variable'],q['shift']
            need(type(stage) is int and 0<=stage<8 and type(i) is int and 0<=i<len(e['variables']),'centering history index')
            need((stage,i)>previous and delta in [-8,-4,-3,-2,-1,1,2,3,4,8],'centering history order/increment')
            need(e['variables'][i]['kind']!='integer_guard','centering altered guard coordinate')
            need(len(q['score'])==3 and all(type(a) is int and a>=0 for a in q['score']),'centering score shape')
            running_rows=[A.sub(row,i,A.add(A.v(i),A.con(delta))) for row in running_rows]
            actual_score=score(running_rows);need(q['score']==actual_score and actual_score<previous_score,'centering actual score/improvement')
            previous_score=actual_score;running[i]=running.get(i,0)+delta;previous=(stage,i)
        need(tc['shifts']==[[i,s] for i,s in sorted(running.items()) if s],'whole composed centering shifts')
    need(d['projected']==projected,'whole chart projected parent')
    poly,used=A.literal(e);need(d['expanded_polynomial']=={'schema':'sparse_integer_polynomial_v1','domain':'unrestricted integers',
        'variables':len(e['variables']),'terms':A.terms(poly)},'every quartic coefficient/header')
    need(A.deg(poly)==4 and used==set(range(len(e['variables']))),'quartic degree/live census')
    expected_metrics=census(A,e,poly);need(d['METRICS']==expected_metrics,'complete actual chart census')
    for oldrow,newrow in zip(projected['residuals'],e['residuals']):
        p=A.norm(newrow)
        for i,s in shifts.items():p=A.sub(p,i,A.add(A.v(i),A.con(-s)))
        need(p==A.norm(oldrow),'whole inverse translation coefficient identity')
    return expected_metrics|{'translations':len(shifts),'equation_sha256':sha(e),'polynomial_sha256':sha(d['expanded_polynomial'])}

def full_check(A,name,d,base):
    result=source_check(A,name,d,base)
    edits=A.factorization(d['pruned_source'],d['factored_source'],d['factorization_certificate']);need(edits==18,'complete accepted Horn edits')
    steps=A.projection(d['factored_source'],d['projected'],d['terminal_elimination_certificate'])
    m=projection_metadata(A,d['factored_source'],d['projected'],d['terminal_elimination_certificate'],d['ENGINE_VERIFICATION'])
    fixtures=inverse_fixtures(A,d['factored_source'],d['projected'],d['terminal_elimination_certificate'])
    charts={n:chart_check(A,d['projected'],d['plain'],n,d[n]) for n in ['plain','centered']}
    history=d['centered']['translation_certificate']['search_history'];initial,_=A.literal(d['plain']['equation'])
    current=(max(map(abs,initial.values()),default=0),len(initial),sum(map(abs,initial.values())));lines=[]
    for stage in range(8):
        changes=[q for q in history if q['pass']==stage]
        if changes:current=tuple(changes[-1]['score'])
        lines.append('pass '+str(stage)+' changes '+str(len(changes))+' score '+str(current)+'\n')
        if not changes:break
    cm={k:charts['centered'][k] for k in ['variables','rows','degree','monomials','height','row_height']}
    lines.append(str(cm)+'\n')
    need(d['CENTER_SEARCH']=={'scope':'Exact accepted finite coordinate-descent policy; no global optimum claim.',
        'transcript':''.join(lines)},'whole deterministic centering transcript')
    return result|{'factorization_edits':edits,'projection_steps':steps,'free_coordinates':d['terminal_elimination_certificate']['unconstrained_removed'],
        'engine':m,'signed_inverse_fixtures':fixtures,'charts':charts}

def load_bundle(folder,full):
    names=['guarded','GUARD_MAP','pruned_source','pruning_certificate']
    if full:names+=['factored_source','factorization_certificate','projected','terminal_elimination_certificate','ENGINE_VERIFICATION','CENTER_SEARCH']
    d={n:get(folder/(n+'.json')) for n in names}
    if full:
        for chart in ['plain','centered']:d[chart]={n:get(folder/chart/(n+'.json')) for n in ['equation','expanded_polynomial','translation_certificate','METRICS','projected']}
    return d

def mutations(A,bundles,base,full):
    controls={}
    def trial(name,fn):
        x=copy.deepcopy(bundles['joint_F_A']);fn(x)
        # Rebind altered endpoints so controls exercise algebra/maps beyond digests.
        x['pruning_certificate']['input_sha256']=sha(x['guarded']);x['pruning_certificate']['output_sha256']=sha(x['pruned_source'])
        if full:
            x['factorization_certificate']['input_sha256']=sha(x['pruned_source']);x['factorization_certificate']['output_sha256']=sha(x['factored_source'])
            x['terminal_elimination_certificate']['input_sha256']=sha(x['factored_source']);x['terminal_elimination_certificate']['output_sha256']=sha(x['projected'])
            for chart in ['plain','centered']:
                x[chart]['translation_certificate']['input_sha256']=sha(x['projected']);x[chart]['translation_certificate']['output_sha256']=sha(x[chart]['equation'])
        try:(full_check if full else source_check)(A,'joint_F_A',x,base)
        except (ValueError,KeyError,IndexError,TypeError) as err:controls[name]={'rejected':True,'reason':str(err)}
        else:raise ValueError('corruption survived '+name)
    trial('body_coefficient',lambda x:x['guarded']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('body_coordinate_metadata',lambda x:x['guarded']['variables'][3].__setitem__('kind','integer_guard'))
    trial('A_guard_wrong_target',lambda x:x['GUARD_MAP']['omitted_guards'][1]['guard'].__setitem__('coordinate',245))
    trial('F_guard_wrong_aux',lambda x:x['GUARD_MAP']['omitted_guards'][0]['guard']['auxiliary'].__setitem__(0,527))
    trial('retained_aux_escape',lambda x:x['guarded']['residuals'][0]['terms'].append([1,[522]]))
    trial('retained_guard_graph',lambda x:x['guarded']['residuals'][-1]['terms'][0].__setitem__(0,999))
    trial('guard_map_compaction',lambda x:x['GUARD_MAP']['retained_variables'][-1].__setitem__(1,0))
    trial('retained_graph_metadata',lambda x:x['GUARD_MAP']['retained_guards'][0]['new']['auxiliary'].__setitem__(0,0))
    trial('omitted_guard_row',lambda x:x['GUARD_MAP']['removed_rows'].__setitem__(1,470))
    trial('private_slack_restore',lambda x:x['pruning_certificate']['dropped_private_slacks'][0]['restoration'][0].__setitem__(0,999))
    trial('private_slack_omitted',lambda x:x['pruning_certificate']['dropped_private_slacks'].pop())
    trial('pruning_aux_index',lambda x:x['pruning_certificate']['dropped_private_slacks'][0].__setitem__('variable',522))
    trial('pruned_body_row',lambda x:x['pruned_source']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('pruned_extra_row',lambda x:x['pruned_source']['residuals'].append({'label':'forged','terms':[[1,[]]]}))
    if full:
        trial('factor_affine_root',lambda x:next(iter(x['factorization_certificate']['square_roots'].values()))[0].__setitem__(0,999))
        trial('factor_edit_omitted',lambda x:x['factorization_certificate']['changes'].pop())
        trial('factor_deleted_definition',lambda x:x['factorization_certificate']['deleted_rows'].pop())
        trial('factored_root_metadata',lambda x:x['factored_source']['variables'][-1].__setitem__('kind','witness'))
        trial('monic_restoration',lambda x:x['terminal_elimination_certificate']['steps'][0]['restoration'][0].__setitem__(0,999))
        trial('monic_step_name',lambda x:x['terminal_elimination_certificate']['steps'][0].__setitem__('name','forged'))
        trial('monic_step_degree',lambda x:x['terminal_elimination_certificate']['steps'][0].__setitem__('restoration_degree',0))
        trial('free_coordinate_partition',lambda x:x['terminal_elimination_certificate']['unconstrained_removed'].pop())
        trial('retained_variable_map',lambda x:x['terminal_elimination_certificate']['retained_original_variables'].pop())
        trial('retained_row_map',lambda x:x['terminal_elimination_certificate']['retained_original_rows'].pop())
        trial('engine_policy',lambda x:x['terminal_elimination_certificate']['metrics'].__setitem__('max_support',8))
        trial('engine_receipt',lambda x:x['ENGINE_VERIFICATION'].__setitem__('verified_steps',0))
        trial('projected_row',lambda x:x['projected']['residuals'][0]['terms'][0].__setitem__(0,999))
        trial('projected_metadata',lambda x:x['projected']['elimination'].__setitem__('certificate','forged.json'))
        trial('plain_shift',lambda x:x['plain']['translation_certificate']['shifts'][0].__setitem__(1,-99))
        trial('plain_quartic',lambda x:x['plain']['expanded_polynomial']['terms'][0].__setitem__(0,999))
        trial('plain_census',lambda x:x['plain']['METRICS'].__setitem__('height',1))
        trial('centered_row',lambda x:x['centered']['equation']['residuals'][0]['terms'][0].__setitem__(0,999))
        trial('centered_quartic',lambda x:x['centered']['expanded_polynomial']['terms'][0].__setitem__(0,999))
        trial('centering_parent',lambda x:x['centered']['translation_certificate'].__setitem__('source_translation_sha256','0'*64))
        trial('centering_history',lambda x:x['centered']['translation_certificate']['search_history'].append({'pass':-1,'variable':0,'shift':1,'score':[0,0,0]}))
        trial('centering_projected_parent',lambda x:x['centered']['projected']['residuals'][0]['terms'][0].__setitem__(0,999))
    return controls

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['source','full'],default='full');ap.add_argument('--data',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    pin_hash=authenticate();A=independent_support();base=parents(A);full=a.mode=='full';folder=a.data or HERE/('full-data' if full else 'data');index=get(folder/'INDEX.json')
    need(index['schema']=='round15_sign_guard_projection_inventory_v1' and index['mode']==a.mode,'inventory mode')
    need(index['source_pins_sha256']==pin_hash,'inventory source pin binding')
    need(index['files']==files(folder,'INDEX.json'),'closed generated inventory')
    need(index['policy']=={'max_support':16,'affine_support':None,'quadratic_first':False,'variants':VARIANTS,'charts':['plain','centered'] if full else []},'exact four-chart policy')
    bundles={n:load_bundle(folder/n,full) for n in VARIANTS};results={n:(full_check if full else source_check)(A,n,d,base) for n,d in bundles.items()}
    expected={}
    for n,d in bundles.items():
        r=results[n];expected[n]={'guarded_variables':r['guarded_variables'],'guarded_rows':r['guarded_rows'],'guards':r['guards'],'pruned_private_slacks':r['private_slacks']}
        if full:expected[n].update({'engine':r['engine'],'plain':{k:r['charts']['plain'][k] for k in ['variables','rows','degree','monomials','height','row_height']},
                                   'centered':{k:r['charts']['centered'][k] for k in ['variables','rows','degree','monomials','height','row_height']}})
    need(index['summary']==expected,'all index summary fields')
    controls=mutations(A,bundles,base,full)
    result={'verified':True,'mode':a.mode,'optimized_python':not __debug__,'audit_sha256':digest(Path(__file__).read_bytes()),
        'source_pins_sha256':pin_hash,'index_sha256':sha(index),'profiles':results,'mutation_controls':controls,
        'scope':'Full integer certificate equivalences and literal quartics; unbounded source calibration is supplied by separately sealed ordinary proofs. No optimality claim.'}
    out=json.dumps(result,sort_keys=True,indent=2)+'\n';need(not a.output.exists() or a.output.read_text()==out,'different existing output')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(out);print(out,end='')
if __name__=='__main__':main()
