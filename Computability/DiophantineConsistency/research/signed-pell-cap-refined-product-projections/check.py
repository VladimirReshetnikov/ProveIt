#!/usr/bin/env python3
"""Independent refined-product projection verifier; CODE ONLY/HOLD for review."""
import argparse,copy,hashlib,importlib.util,json,sys
from collections import Counter
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/'research/signed-pell-cap-refined-product-source'
SOURCE_SEAL='de311c82c61e7fee99e816c971256d662a28e620c51807ca7d5ef3611240ea93'
SOURCE_FILES=['source.json','guarded.json','domain.json','TRANSFORM.json','CALIBRATION_BINDING.json']
BASELINES=[('cap_plain','research/signed-pell-cap-projections','data/plain'),
 ('cap_centered','research/signed-pell-cap-projections','data/centered'),
 ('grouped_centered','research/signed-pell-cap-grouped-quartic','data'),
 ('helper_plain','research/round15-helper-guard-projections','full-data/joint_helper/plain'),
 ('helper_centered','research/round15-helper-guard-projections','full-data/joint_helper/centered')]
POLICY=dict(max_support=16,affine_support=None,quadratic_first=False,charts=['plain','centered'],private_slack_pruning=False)
def need(ok,why):
    if not ok:raise ValueError(why)
def get(p):return json.loads(p.read_bytes())
def canon(d):return (json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(d):return digest(canon(d))
def files(p,skip):return {str(q.relative_to(p)):digest(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and str(q.relative_to(p))!=skip}
def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole input '+n)
    for n,h in pins['vendor'].items():need(digest((HERE/'vendor'/n).read_bytes())==h,'whole vendor '+n)
    for n,h in pins['core'].items():need(digest((HERE/n).read_bytes())==h,'whole author core '+n)
    for n,h in pins['closed_dependencies'].items():
        folder=ROOT/n;need(digest((folder/'MANIFEST.json').read_bytes())==h,'closed dependency pin '+n)
        declared=get(folder/'MANIFEST.json')['files'];actual=files(folder,'MANIFEST.json')
        expected={name:dict(bytes=(folder/name).stat().st_size,sha256=value) if isinstance(declared.get(name),dict) else value for name,value in actual.items()}
        need(declared==expected,'whole closed dependency, hashes and byte counts '+n)
    need(digest((SOURCE/'MANIFEST.json').read_bytes())==SOURCE_SEAL,'accepted complete refined-product source')
    if (HERE/'MANIFEST.json').exists():need(get(HERE/'MANIFEST.json')['files']==files(HERE,'MANIFEST.json'),'closed new packet')
    return digest((HERE/'SOURCE_PINS.json').read_bytes())
def independent_support():
    # This is the sole nonstdlib import. It imports no producer or optimizer.
    spec=importlib.util.spec_from_file_location('cap_independent_support',HERE/'vendor/check_direct.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
def source_check(A,d):
    for n in SOURCE_FILES:need(d[n[:-5]]==get(SOURCE/n),'whole sealed literal refined-product artifact '+n)
    body,guarded,domain,transform=(d[k] for k in ['source','guarded','domain','TRANSFORM']);e=copy.deepcopy(body);N=len(body['variables'])
    parent=get(ROOT/'research/signed-pell-cap-refined-source/source.json')
    need(body['variables'][:399]==parent['variables'] and body['residuals'][:334]==parent['residuals'],'whole original refined body unchanged')
    need(body['domain']==guarded['domain']=='unrestricted integers' and not any(v['name'].endswith('.YminusK') for v in body['variables']),'integer domain and no second slack pruning')
    seen=set();kinds=Counter();oldguardids=[]
    for g in domain['guards']:
        kinds[g['kind']]+=1;expr=A.norm(g['expression']);a,b,c=g['auxiliary'];row=dict(label=guarded['residuals'][g['row']]['label'],terms=A.terms(A.add(expr,{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})))
        need(len({a,b,c})==3 and not seen.intersection([a,b,c]),'all distinct graph auxiliary triples');seen|={a,b,c}
        if g['row']<len(body['residuals']):
            need(g['kind']=='cap_square_bound' and g['row']==217 and g['auxiliary']==[396,397,398],'sole embedded cap graph')
            want=A.add(A.mul(A.v(387),A.v(387)),A.con(-1),*[A.sc(A.mul(A.v(s['pair'][1]),A.v(s['pair'][1])),-1) for s in transform['all15_signed_targets']])
            need(expr==want and row==body['residuals'][217],'whole unoriented cap square bound')
        else:
            need(g['auxiliary']==list(range(len(e['variables']),len(e['variables'])+3)) and g['row']==len(e['residuals']),'entire appended graph row and coordinate order')
            if 'original_guard_index' in g:
                j=g['original_guard_index'];oldguardids.append(j);stem='guard'+str(j);need(row['label']=='domain_guard.'+str(j),'actual old guard label')
                if g['kind']=='nonnegative':need(expr==A.v(g['coordinate']),'actual retained scalar expression')
                else:need(g['kind']=='paired_interval' and expr==A.mul(A.v(g['pair'][0]),A.v(g['pair'][1])),'actual paired product expression')
            elif g['kind']=='comparison_base_lower':
                stem='helper_base_lower';need(expr==A.add(A.v(255),A.con(-4)) and row['label']=='domain_guard.helper_base_lower','whole reflected-helper replacement')
            else:
                stem='scalar_product_positive';need(g['kind']=='strict_index_product' and expr==A.add(A.v(405),A.con(-1)) and row['label']=='domain_guard.scalar_product_positive','whole strict product expression')
                need(g['factors']==[dict(coordinate=i,shift=1) for i in range(16,24)],'all eight scalar factors')
            e['variables'] += [dict(name=stem+'.'+s,kind='integer_guard') for s in ['a','b','c']];e['residuals'].append(row)
        need(all([i for i,r in enumerate(guarded['residuals']) if any(v in m for c,m in r['terms'])]==[g['row']] for v in g['auxiliary']),'whole graph private occurrences')
    need(e==guarded,'complete guarded extension including every variable and row')
    need(oldguardids==[0,3,4,5,15,16,17,18,19,20,21,22,23,24,26,31,32,33,34,35,36,37],'exact original guard policy')
    need(kinds==Counter(nonnegative=15,paired_interval=7,cap_square_bound=1,comparison_base_lower=1,strict_index_product=1),'all25 graph families')
    scalar={g['coordinate'] for g in domain['guards'] if g['kind']=='nonnegative'}
    need(not scalar.intersection({1,3,246,251,252,387}|set(range(16,25))),'omitted scalar signs not reintroduced')
    factors={}
    for offset in range(7):
        v=399+offset;p=A.norm(body['residuals'][334+offset]);f=A.solved(p,v)
        want=A.mul(A.add(A.v(16),A.con(1)),A.add(A.v(17),A.con(1))) if offset==0 else A.mul(A.v(v-1),A.add(A.v(17+offset),A.con(1)))
        need(f==want and body['residuals'][334+offset]['label']=='scalar_product.p'+str(offset+2)+'_definition','each exact original product row')
        for previous,value in factors.items():f=A.sub(f,previous,value)
        factors[v]=f
    product=A.con(1)
    for i in range(16,24):product=A.mul(product,A.add(A.v(i),A.con(1)))
    need(factors[405]==product,'whole unique eight-factor product extension')
    atoms=transform['all37_frame_atoms'];want=A.add(A.v(245),A.con(-4),*[A.sc(A.mul(A.norm(a['affine']),A.norm(a['affine'])),-2) for a in atoms])
    need(A.norm(body['residuals'][333])==want,'whole unchanged absolute frame')
    calls=[226,234,239,247,253,258,266,271,276,281,286,291,296,301,306,311,316,321]
    for call,request in enumerate(transform['all18_actual_power_requests']):
        need(request['call']==call and request['row']==calls[call] and request['complete_row']==body['residuals'][calls[call]] and request['label']=='pow'+str(call)+'.power_congruence','all18 actual call row memberships')
        need(all(any(A.norm(request['ports'][role])==A.norm(a['affine']) for a in atoms) for role in ['base','exponent','output']),'all54 exact original frame ports')
    need(transform['whole_refined_body_pointwise_fixed'] and transform['helper_normalization_is_temporary'] and not transform['A_or_C_positive_assumed'] and not transform['h_changes_in_product_maps'],'unchanged full ordinary sign/calibration interface')
    A.literal(body);A.literal(guarded)
    expected=dict(schema='refined_product_projection_source_binding_v1',source_manifest_sha256=SOURCE_SEAL,
        whole_literal_artifacts={n:digest((SOURCE/n).read_bytes()) for n in SOURCE_FILES},ordinary_manifest_sha256=body['ordinary_manifest_sha256'],
        source_calibration=get(SOURCE/'CALIBRATION_BINDING.json'),single_product_policy=True,whole_refined_body_coordinates_fixed=399,whole_refined_body_rows_fixed=334,
        F_A_C_V_d_signs_not_reintroduced=True,old_private_slack_pruning_applied=False,private_Pell_tuple_identity_to_baselines_claimed=False)
    need(d['SOURCE_BINDING']==expected,'whole accepted source-calibration boundary')
    return dict(source_manifest_sha256=SOURCE_SEAL,whole_literal_binding=True,guards=dict(kinds),native_calibration='Whole sealed source restored after Horn inverse; use its complete signed ordinary theorem and witness maps.')
def horn_check(A,src,dst,c,wm):
    need(set(c)=={'schema','input_sha256','output_sha256','square_variables','square_roots','product_chain','changes','deleted_rows','guard_variables','new_root','new_row','identity','guard_identity'} and c['schema']=='signed_horn_factorization_v1','entire Horn certificate header')
    need(c['identity']=='(product(L_i^2))*(B^2+G^2) = (product(L_i))^2*(B^2+G^2)' and c['guard_identity']=='((c-a)^2*(c-b)^2-D^2)^2 = (((c-a)*(c-b))^2-D^2)^2','exact coefficient-uniform identity metadata')
    need(set(c['square_roots'])=={str(s) for s in c['square_variables']} and set(c['guard_variables'])=={'h','old_second_square','g','old_D_square'} and c['deleted_rows']==sorted(set(c['deleted_rows'])),'complete Horn root/private inventories')
    need(A.factorization(src,dst,c)==18,'all eighteen exact accepted Horn rewrites')
    oldrows=[A.norm(r) for r in src['residuals']];newrows=[A.norm(r) for r in dst['residuals']];sq=c['square_variables'];g=c['guard_variables'];h,u,z,d=(g[k] for k in ['h','old_second_square','g','old_D_square'])
    defs={s:next(i for i,r in enumerate(src['residuals']) if r['label']=='nonnegative_square_difference' and oldrows[i].get((s,))==1) for s in sq}
    pr=next(i for i,p in enumerate(oldrows) if p.get((z,)) in [-1,1] and not any(z in m for m in p if m!=(z,)) and A.solved(p,z)==A.mul(A.v(h),A.v(u)))
    dr=next(i for i,p in enumerate(oldrows) if p.get((d,)) in [-1,1] and not any(d in m for m in p if m!=(d,)))
    targets={s:defs[s] for s in sq[:9]+sq[13:15]+[h,u,sq[11]]};targets.update({z:pr,d:dr});targets.update({v:r for r,v in c['product_chain']});deleted=set(c['deleted_rows']);rm={i:j for j,i in enumerate(i for i in range(len(oldrows)+1) if i not in deleted)}
    forward={v:rm[r] for v,r in targets.items() if v not in {u,d}};forward[c['new_root']]=len(newrows)-1
    def rules(ds,rows):
        remaining=dict(ds);out=[]
        while remaining:
            choices=[]
            for v,r in remaining.items():
                f=A.solved(rows[r],v)
                if not {i for m in f for i in m}&set(remaining):choices.append((v,r,f))
            need(choices,'acyclic complete Horn witness map');v,r,f=min(choices,key=lambda q:q[0]);del remaining[v];out.append(dict(coordinate=v,row=r,restoration=A.terms(f)))
        return out
    fr,rr=rules(forward,newrows),rules(targets,oldrows);private=sorted(targets);preserved=sorted(set(range(len(src['variables'])))-set(private))
    need(not set(private).intersection({1,3,246,251,252,387}|set(range(16,25))|set(range(399,406))),'Horn private overwrites avoid all new product/sign ports')
    expected=dict(schema='signed_cap_horn_existential_maps_v1',source_sha256=sha(src),factored_sha256=sha(dst),preserved_source_coordinates=preserved,overwritten_source_coordinates=private,
        source_to_factored=dict(copy_source_coordinates=list(range(len(src['variables']))),initialize_factored_private_to_zero=sorted({u,d}),restorations=fr),
        factored_to_source=dict(discard_factored_coordinates=[c['new_root']],copy_source_coordinates=list(range(len(src['variables']))),restorations=rr),
        full_old_witness_identity_claimed=False,projection_free_coordinates='Use every actual unconstrained_removed coordinate, without assuming its cardinality. Initialize it to zero for the factored chart, then apply the reverse Horn overwrite rules for an old-source witness.',
        identity_scope='Monic projection identities hold relative to the factored residual ideals. Horn maps preserve the listed exposed coordinates and reconstruct private witnesses in each direction; the maps need not be inverse on old private witnesses.')
    need(wm==expected,'every Horn overwrite rule and its exact existential scope')
    need(not any(i in {u,d} for p in newrows for m in p for i in m),'obsolete factored coordinates are actually unused')
    # This free-coefficient identity proves the entire small Horn boundary.
    product=A.con(1);oldproduct=A.con(1)
    for i in range(11):product=A.mul(product,A.v(i));oldproduct=A.mul(oldproduct,A.mul(A.v(i),A.v(i)))
    r,s,D2,B2=map(A.v,[11,12,13,14]);oldguard=A.add(A.mul(A.mul(r,r),A.mul(s,s)),A.sc(D2,-1));newguard=A.add(A.mul(A.mul(r,s),A.mul(r,s)),A.sc(D2,-1))
    need(A.mul(oldproduct,A.add(A.mul(oldguard,oldguard),B2))==A.mul(A.mul(product,product),A.add(A.mul(newguard,newguard),B2)),'whole coefficient-uniform Horn/guard identity')
    fixtures=[]
    for seed in [7,19]:
        original={i:((i*seed+3)%11)-5 for i in range(len(src['variables']))}
        for q in rr:original[q['coordinate']]=evaluate(A.norm(q['restoration']),original)
        factored=dict(original);factored[c['new_root']]=0
        for i in [u,d]:factored[i]=0
        for q in fr:factored[q['coordinate']]=evaluate(A.norm(q['restoration']),factored)
        restored={i:factored[i] for i in range(len(src['variables']))}
        for q in rr:restored[q['coordinate']]=evaluate(A.norm(q['restoration']),restored)
        need(all(original[i]==factored[i]==restored[i] for i in preserved),'all exposed Horn coordinates preserved')
        need(factored[c['new_root']]==original[c['product_chain'][-1][1]],'actual old/new whole Horn boundary')
        need(all(evaluate(oldrows[q['row']],original)==evaluate(oldrows[q['row']],restored)==0 for q in rr),'all old Horn definitions restored')
        need(all(evaluate(newrows[q['row']],factored)==0 for q in fr),'all new Horn definitions restored')
        for i,p in enumerate(oldrows):need(evaluate(p,original)==evaluate(p,restored) and (i in deleted or evaluate(p,original)==evaluate(newrows[rm[i]],factored)),'every actual exposed residual under both Horn maps')
        fixtures.append(dict(seed=seed,whole_source_rows=len(oldrows),whole_factored_rows=len(newrows),all_preserved_coordinates=True))
    return dict(edits=18,full_old_witness_identity_claimed=False,coefficient_uniform_Horn_identity=True,private_overwrites=private,exposed_coordinates=preserved,fixtures=fixtures)
def inverse_fixtures(A,src,dst,c):
    records=[]
    for seed,free in [(7,0),(19,-5),(23,3)]:
        target=[((i*seed+3)%11)-5 for i in range(len(dst['variables']))];values={i:target[j] for j,i in enumerate(c['retained_original_variables'])}
        for i in c['unconstrained_removed']:values[i]=free
        for q in reversed(c['steps']):values[q['variable']]=evaluate(A.norm(q['restoration']),values)
        need(set(values)==set(range(len(src['variables']))),'all factored inverse coordinates, including arbitrary actual free coordinates')
        kept={r:evaluate(A.norm(dst['residuals'][j]),dict(enumerate(target))) for j,r in enumerate(c['retained_original_rows'])}
        for i,row in enumerate(src['residuals']):need(evaluate(A.norm(row),values)==kept.get(i,0),'every factored inverse residual '+str(i))
        records.append(dict(seed=seed,free_value=free,actual_free_coordinates=list(c['unconstrained_removed']),rows_checked=len(src['residuals'])))
    return records

def census(A,e,p):
    return {'variables':len(e['variables']),'rows':len(e['residuals']),'degree':A.deg(p),'monomials':len(p),
        'height':max(map(abs,p.values()),default=0),'row_height':max((abs(c) for row in e['residuals'] for c,m in row['terms']),default=0)}


def projection_metadata(A,src,dst,c,receipt):
    need(set(c)=={'schema','input_sha256','output_sha256','steps','unconstrained_removed','retained_original_variables','retained_original_rows','metrics'},'entire projection certificate header')
    need(c['schema']=='integer_quadratic_elimination_v1','projection schema')
    for q in c['steps']:
        need(set(q)=={'row_id','variable','name','kind','restoration','restoration_degree'},'entire projection step metadata')
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
        need(set(tc)=={'schema','input_sha256','output_sha256','shifts','convention','search_history','source_translation_sha256','search_scope'},'entire centered translation header')
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
            need(set(q)=={'pass','variable','shift','score'},'entire centering history entry')
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

def full_check(A,d):
    source=source_check(A,d);horn=horn_check(A,d['guarded'],d['factored_source'],d['factorization_certificate'],d['HORN_WITNESS_MAP'])
    c=d['terminal_elimination_certificate'];steps=A.projection(d['factored_source'],d['projected'],c)
    engine=projection_metadata(A,d['factored_source'],d['projected'],c,d['ENGINE_VERIFICATION']);fixtures=inverse_fixtures(A,d['factored_source'],d['projected'],c)
    charts={n:chart_check(A,d['projected'],d['plain'],n,d[n]) for n in ['plain','centered']}
    history=d['centered']['translation_certificate']['search_history'];p,_=A.literal(d['plain']['equation']);score=(max(map(abs,p.values()),default=0),len(p),sum(map(abs,p.values())));lines=[]
    for stage in range(8):
        changes=[q for q in history if q['pass']==stage]
        if changes:score=tuple(changes[-1]['score'])
        lines.append('pass '+str(stage)+' changes '+str(len(changes))+' score '+str(score)+'\n')
        if not changes:break
    cm={k:charts['centered'][k] for k in ['variables','rows','degree','monomials','height','row_height']};lines.append(str(cm)+'\n')
    need(d['CENTER_SEARCH']==dict(scope='Exact accepted finite coordinate-descent policy; no global optimum claim.',transcript=''.join(lines)),'whole accepted deterministic centering transcript')
    comparison={}
    for alias,directory,relative in BASELINES:
        folder=ROOT/directory/relative;raw=get(folder/'METRICS.json');eq=get(folder/'equation.json');poly,used=A.literal(eq);old=census(A,eq,poly)
        need(get(folder/'expanded_polynomial.json')==dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',variables=len(eq['variables']),terms=A.terms(poly)),'every coefficient of complete baseline '+alias)
        if alias=='grouped_centered':
            expected_raw=dict(declared_variables=len(eq['variables']),used_variables=sorted(used),unconstrained_variables=sorted(set(range(len(eq['variables'])))-used),residuals=len(eq['residuals']),
                residual_degree=max((A.deg(A.norm(r)) for r in eq['residuals']),default=0),degree=A.deg(poly),terms=len(poly),height=old['height'],residual_height=old['row_height'],largest_residual_support=max((len(A.norm(r)) for r in eq['residuals']),default=0))
        else:expected_raw=old
        need(raw==expected_raw and used==set(range(len(eq['variables']))),'all actual baseline measurements '+alias)
        comparison[alias]=dict(parent_directory=directory,parent_manifest_sha256=digest((ROOT/directory/'MANIFEST.json').read_bytes()),relative_directory=relative,
            complete_baseline_files={n:digest((folder/n).read_bytes()) for n in ['equation.json','expanded_polynomial.json','METRICS.json']},literal_baseline_metrics=raw,normalized_metrics=old,
            charts={chart:dict(new_metrics={k:charts[chart][k] for k in old},delta={k:charts[chart][k]-old[k] for k in old}) for chart in ['plain','centered']})
    expected=dict(schema='refined_product_complete_alternatives_v1',source_manifest_sha256=SOURCE_SEAL,baselines=comparison,
        polynomial_identity_claimed=False,old_private_Pell_tuple_identity_claimed=False,scope='Complete calibrated cap, grouped cap and helper charts; numerical differences only, no private tuple or polynomial identity.')
    need(d['COMPARISON']==expected,'all five complete alternatives and actual deltas')
    wm=d['HORN_WITNESS_MAP']
    maps=dict(schema='refined_product_composed_integer_maps_v1',source_coordinates=len(d['guarded']['variables']),factored_coordinates=len(d['factored_source']['variables']),
        source_to_factored=wm['source_to_factored'],factored_to_source=wm['factored_to_source'],Horn_preserved_source_coordinates=wm['preserved_source_coordinates'],
        projection_retained_original_variables=c['retained_original_variables'],projection_retained_original_rows=c['retained_original_rows'],actual_projection_free_coordinates=c['unconstrained_removed'],reverse_monic_restorations=list(reversed(c['steps'])),
        charts={chart:dict(integer_domain='unrestricted integers',convention='projected_old=chart_new+shift',shifts=d[chart]['translation_certificate']['shifts'],chart_coordinate_metadata=d[chart]['equation']['variables']) for chart in ['plain','centered']},
        inverse_order=['inverse_integer_translation','assign_every_actual_free_coordinate_zero','reverse_all_monic_restorations','overwrite_original_Horn_private_witnesses','apply_sealed_source_calibration'],
        forward_order=['construct_sealed_source_witness','overwrite_factored_Horn_private_witnesses','retain_actual_projected_coordinates','subtract_integer_translation'],whole_old_Horn_private_tuple_identity_claimed=False)
    need(d['COMPOSED_MAPS']==maps,'every complete composed integer witness map')
    prior={name+'.json':sha(value) for name,value in d.items() if name not in ['plain','centered','ENDPOINT_BINDING']}
    for chart in ['plain','centered']:
        prior.update({chart+'/'+name+'.json':sha(value) for name,value in d[chart].items()})
    # Source copies retain the accepted pretty bytes; all other artifacts use
    # the canonical compact serialization checked at the inventory boundary.
    prior.update({name:digest((SOURCE/name).read_bytes()) for name in SOURCE_FILES})
    endpoint=dict(schema='refined_product_complete_endpoint_calibration_v1',source_manifest_sha256=SOURCE_SEAL,ordinary_manifest_sha256=d['source']['ordinary_manifest_sha256'],
        source_calibration_sha256=digest((SOURCE/'CALIBRATION_BINDING.json').read_bytes()),source_pins_sha256=digest((HERE/'SOURCE_PINS.json').read_bytes()),all_prior_generated_files=prior,
        equivalence_chain=['sealed_refined_product_source_calibration','actual_Horn_existential_maps','actual_monic_and_free_coordinate_maps','integer_chart_bijections','full_literal_sum_of_squares'],
        reconstructed_source_is_whole_guarded_tuple=True,native_calibration_applied_only_after_full_source_restoration=True,all_source_product_frame_and_sign_interfaces_unchanged=True,new_unbounded_or_Lean_theorem_claimed=False)
    need(d['ENDPOINT_BINDING']==endpoint,'whole finite endpoint and source calibration closure')
    return dict(source=source,Horn=horn,projection_steps=steps,actual_free_coordinates=list(c['unconstrained_removed']),engine=engine,signed_inverse_fixtures=fixtures,charts=charts,complete_baselines=comparison,complete_endpoint_calibration=True)
def load_bundle(folder):
    names=['source','guarded','domain','TRANSFORM','CALIBRATION_BINDING','SOURCE_BINDING','factored_source','factorization_certificate','HORN_WITNESS_MAP','projected','terminal_elimination_certificate','ENGINE_VERIFICATION','CENTER_SEARCH','COMPARISON','COMPOSED_MAPS','ENDPOINT_BINDING'];d={n:get(folder/(n+'.json')) for n in names}
    for chart in ['plain','centered']:d[chart]={n:get(folder/chart/(n+'.json')) for n in ['equation','expanded_polynomial','translation_certificate','METRICS','projected']}
    return d
def mutations(A,original):
    controls={}
    def trial(name,fn):
        d=copy.deepcopy(original);fn(d)
        # Rebind hashes after mutations so algebra/map checks are exercised.
        d['factorization_certificate'].update(input_sha256=sha(d['guarded']),output_sha256=sha(d['factored_source']))
        d['terminal_elimination_certificate'].update(input_sha256=sha(d['factored_source']),output_sha256=sha(d['projected']))
        d['HORN_WITNESS_MAP'].update(source_sha256=sha(d['guarded']),factored_sha256=sha(d['factored_source']))
        for chart in ['plain','centered']:d[chart]['translation_certificate'].update(input_sha256=sha(d['projected']),output_sha256=sha(d[chart]['equation']))
        try:full_check(A,d)
        except (ValueError,KeyError,IndexError,TypeError) as err:controls[name]=dict(rejected=True,reason=str(err))
        else:raise ValueError('actual corruption accepted '+name)
    trial('changed_source_body',lambda d:d['source']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('changed_guarded_body',lambda d:d['guarded']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('changed_product_graph',lambda d:d['domain']['guards'][-1]['expression'][0].__setitem__(0,0))
    trial('changed_product_factor',lambda d:d['source']['residuals'][334]['terms'][0].__setitem__(0,999))
    trial('changed_original_target',lambda d:d['TRANSFORM']['all15_signed_targets'][0]['target'][0].__setitem__(0,15))
    trial('wrong_call11_membership',lambda d:d['TRANSFORM']['all18_actual_power_requests'][11].__setitem__('row',296))
    trial('wrong_call14_membership',lambda d:d['TRANSFORM']['all18_actual_power_requests'][14].__setitem__('row',311))
    trial('changed_frame_atom',lambda d:d['TRANSFORM']['all37_frame_atoms'][0]['affine'].append([1,[399]]))
    trial('false_signed_A_assumption',lambda d:d['TRANSFORM'].__setitem__('A_or_C_positive_assumed',True))
    trial('false_old_Pell_tuple_identity',lambda d:d['SOURCE_BINDING'].__setitem__('private_Pell_tuple_identity_to_baselines_claimed',True))
    trial('changed_source_calibration',lambda d:d['CALIBRATION_BINDING'].__setitem__('whole_refined_body_pointwise_fixed',False))
    trial('Horn_root',lambda d:next(iter(d['factorization_certificate']['square_roots'].values()))[0].__setitem__(0,999))
    trial('Horn_certificate_schema',lambda d:d['factorization_certificate'].__setitem__('schema','forged'))
    trial('Horn_edit_missing',lambda d:d['factorization_certificate']['changes'].pop())
    trial('Horn_deleted_definition',lambda d:d['factorization_certificate']['deleted_rows'].pop())
    trial('Horn_factored_coordinate_kind',lambda d:d['factored_source']['variables'][-1].__setitem__('kind','witness'))
    trial('Horn_reverse_overwrite',lambda d:d['HORN_WITNESS_MAP']['factored_to_source']['restorations'][0]['restoration'][0].__setitem__(0,0))
    trial('Horn_exposed_coordinate_map',lambda d:d['HORN_WITNESS_MAP']['preserved_source_coordinates'].pop())
    trial('false_all_old_witness_identity',lambda d:d['HORN_WITNESS_MAP'].__setitem__('full_old_witness_identity_claimed',True))
    trial('monic_restoration',lambda d:d['terminal_elimination_certificate']['steps'][0]['restoration'][0].__setitem__(0,0))
    trial('monic_step_name',lambda d:d['terminal_elimination_certificate']['steps'][0].__setitem__('name','forged'))
    trial('monic_degree_metadata',lambda d:d['terminal_elimination_certificate']['steps'][0].__setitem__('restoration_degree',-1))
    trial('arbitrary_actual_free_partition',lambda d:d['terminal_elimination_certificate']['unconstrained_removed'].append(0))
    trial('retained_coordinate_map',lambda d:d['terminal_elimination_certificate']['retained_original_variables'].pop())
    trial('retained_row_map',lambda d:d['terminal_elimination_certificate']['retained_original_rows'].pop())
    trial('changed_engine_policy',lambda d:d['terminal_elimination_certificate']['metrics'].__setitem__('max_support',8))
    trial('unlicensed_projection_metadata',lambda d:d['terminal_elimination_certificate'].__setitem__('old_private_witness_identity',True))
    trial('changed_engine_receipt',lambda d:d['ENGINE_VERIFICATION'].__setitem__('verified_steps',-1))
    trial('changed_projected_row',lambda d:d['projected']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('changed_projected_metadata',lambda d:d['projected']['elimination'].__setitem__('certificate','forged'))
    trial('plain_translation',lambda d:d['plain']['translation_certificate']['shifts'][0].__setitem__(1,-99))
    trial('plain_quartic',lambda d:d['plain']['expanded_polynomial']['terms'][0].__setitem__(0,0))
    trial('plain_census',lambda d:d['plain']['METRICS'].__setitem__('height',-1))
    trial('centered_row',lambda d:d['centered']['equation']['residuals'][0]['terms'][0].__setitem__(0,0))
    trial('centered_quartic',lambda d:d['centered']['expanded_polynomial']['terms'][0].__setitem__(0,0))
    trial('centering_parent',lambda d:d['centered']['translation_certificate'].__setitem__('source_translation_sha256','0'*64))
    trial('centering_history',lambda d:d['centered']['translation_certificate']['search_history'].append(dict(pass_=-1,variable=0,shift=1,score=[0,0,0])))
    trial('centering_projected_parent',lambda d:d['centered']['projected']['residuals'][0]['terms'][0].__setitem__(0,999))
    trial('comparison_delta',lambda d:d['COMPARISON']['baselines']['cap_centered']['charts']['plain']['delta'].__setitem__('variables',999))
    trial('missing_grouped_alternative',lambda d:d['COMPARISON']['baselines'].pop('grouped_centered'))
    trial('false_comparison_polynomial_identity',lambda d:d['COMPARISON'].__setitem__('polynomial_identity_claimed',True))
    trial('composed_actual_free_map',lambda d:d['COMPOSED_MAPS']['actual_projection_free_coordinates'].append(0))
    trial('composed_reverse_Horn_order',lambda d:d['COMPOSED_MAPS']['inverse_order'].reverse())
    trial('composed_monic_rule',lambda d:d['COMPOSED_MAPS']['reverse_monic_restorations'][0]['restoration'][0].__setitem__(0,999))
    trial('endpoint_source_calibration',lambda d:d['ENDPOINT_BINDING'].__setitem__('source_manifest_sha256','0'*64))
    trial('endpoint_missing_generated_quartic',lambda d:d['ENDPOINT_BINDING']['all_prior_generated_files'].pop('centered/expanded_polynomial.json'))
    return controls
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--data',type=Path,default=HERE/'data');p.add_argument('--output',type=Path,required=True);a=p.parse_args();pinhash=authenticate();A=independent_support();index=get(a.data/'INDEX.json')
    need(set(index)=={'schema','source_pins_sha256','policy','summary','files'} and index['schema']=='refined_product_two_chart_projection_inventory_v1' and index['source_pins_sha256']==pinhash,'exact generated inventory header')
    expected_files={n+'.json' for n in ['source','guarded','domain','TRANSFORM','CALIBRATION_BINDING','SOURCE_BINDING','factored_source','factorization_certificate','HORN_WITNESS_MAP','projected','terminal_elimination_certificate','ENGINE_VERIFICATION','CENTER_SEARCH','COMPARISON','COMPOSED_MAPS','ENDPOINT_BINDING']}|{chart+'/'+n+'.json' for chart in ['plain','centered'] for n in ['equation','expanded_polynomial','translation_certificate','METRICS','projected']}
    need(set(index['files'])==expected_files,'entire specified generated artifact inventory')
    need(index['policy']==POLICY and index['files']==files(a.data,'INDEX.json'),'exact two-chart policy and closed literal generated inventory')
    for n in SOURCE_FILES:need((a.data/n).read_bytes()==(SOURCE/n).read_bytes(),'whole byte-exact sealed source copy '+n)
    for n in expected_files-set(SOURCE_FILES):need((a.data/n).read_bytes()==canon(get(a.data/n)),'whole canonical generated artifact '+n)
    d=load_bundle(a.data);result=full_check(A,d);summary=dict(engine=result['engine'],plain={k:result['charts']['plain'][k] for k in ['variables','rows','degree','monomials','height','row_height']},centered={k:result['charts']['centered'][k] for k in ['variables','rows','degree','monomials','height','row_height']});need(index['summary']==summary,'every actual inventory census field')
    controls=mutations(A,d);record=dict(status='PASS',optimized_python=bool(sys.flags.optimize),checker_sha256=digest(Path(__file__).read_bytes()),source_pins_sha256=pinhash,index_sha256=sha(index),profile=result,mutation_controls=controls,scope='Whole literal quartics and integer Horn/monic/translation equivalences at the completely calibrated refined-product source. No old-private-witness identity or global optimality claim.')
    target=a.output.resolve();need(not any(target.is_relative_to((ROOT/n).resolve()) for n in get(HERE/'SOURCE_PINS.json')['closed_dependencies']),'never write closed dependencies')
    need(not (HERE/'MANIFEST.json').exists() or not target.is_relative_to(HERE),'receipt outside sealed packet')
    out=(json.dumps(record,sort_keys=True,indent=2)+'\n').encode();need(not a.output.is_symlink() and (not a.output.exists() or a.output.read_bytes()==out),'refuse changed receipt overwrite');a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(out);print(out.decode(),end='')
if __name__=='__main__':main()

