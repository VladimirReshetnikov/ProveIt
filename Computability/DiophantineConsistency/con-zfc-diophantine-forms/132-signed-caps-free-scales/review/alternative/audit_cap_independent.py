#!/usr/bin/env python3
"""Independent wave16 finite audit, no producer imports.
The polynomial kernel and Horn/projection replay are copied from the prior
independently reviewed wave15 checker, with a fresh strict cap-source audit.
All decisions use explicit checks (not Python assert), including under -O.
"""
import argparse, copy, hashlib, json, math
from collections import defaultdict, Counter
from pathlib import Path

def need(c,m):
    if not c: raise ValueError(m)
def load(p): return json.loads(Path(p).read_text())
def source_dir(base):
    choices=[base/'direct/derived16_signed_shell',base/'source',base]
    return next(p for p in choices if (p/'mixed_source.json').is_file() and (p/'domain_certificate.json').is_file())
def canon(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(x): return hashlib.sha256(canon(x)).hexdigest()
def poly(t):
    d=defaultdict(int)
    for c,m in t:
        need(isinstance(c,int) and all(isinstance(v,int) and v>=0 for v in m),'noninteger coefficient/index')
        d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}
def terms(p): return [[c,list(m)] for m,c in sorted(p.items())]
def add(*ps):
    d=defaultdict(int)
    for p in ps:
        for m,c in p.items(): d[m]+=c
    return {m:c for m,c in d.items() if c}
def neg(p): return {m:-c for m,c in p.items()}
def mul(a,b):
    d=defaultdict(int)
    for m,c in a.items():
        for n,e in b.items(): d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}
def var(i): return {(i,):1}
def degree(p): return max(map(len,p),default=0)
def substitute(p,v,f):
    d={}
    for m,c in p.items():
        term={():c}
        for u in m: term=mul(term,f if u==v else var(u))
        d=add(d,term)
    return d
def rhs(p,v):
    c=p.get((v,),0)
    if c not in (-1,1): return None
    if any(v in m for m in p if m!=(v,)): return None
    return {m:-a*c for m,a in p.items() if m!=(v,)}
def evalpoly(p,values):
    return sum(c*math.prod(values[i] for i in m) for m,c in p.items())
def lower(p,bounds):
    if any(c<0 for c in p.values()): return None
    s=0
    for m,c in p.items():
        q=c
        for v,k in Counter(m).items():
            if v in bounds and bounds[v]>=0: q*=bounds[v]**k
            elif k%2==0: q=0
            else: return None
        s+=q
    return min(64,s)
def closure(rows,initial):
    bounds=dict(initial);steps=[]
    for sweep in range(1000):
        changed=False
        for rid,p in enumerate(rows):
            for m in p:
                if len(m)!=1:continue
                v=m[0];f=rhs(p,v)
                if f is None:continue
                b=lower(f,bounds)
                if b is not None and b>bounds.get(v,-10**30):
                    old=bounds.get(v);bounds[v]=b;changed=True
                    steps.append({'row':rid,'variable':v,'lower_bound':b,'rhs':terms(f),
                                  'dependencies':[[u,bounds[u]] for u in sorted({u for mon in f for u in mon if u!=v and u in bounds})]})
        if not changed:return bounds,steps
    raise ValueError('bound closure did not terminate')
def check_factor(source,cand):
    out=load(cand/'factored_source.json');c=load(cand/'factorization_certificate.json')
    need(digest(source)==c['input_sha256'] and digest(out)==c['output_sha256'],'factor hashes')
    rows=[poly(r['terms']) for r in source['residuals']]; sq=c['square_variables'];roots={int(i):poly(t) for i,t in c['square_roots'].items()}
    need(len(sq)==17 and set(roots)==set(sq),'square inventory')
    defs={}
    for v in sq:
        ds=[j for j,p in enumerate(rows) if rhs(p,v)==mul(roots[v],roots[v])]
        need(len(ds)==1,'factor root not exact or not unique');defs[v]=ds[0]
    chain=c['product_chain'];need(len(chain)==11,'Horn chain count')
    fs=sq[:9]+['bundle',sq[13],sq[14]];prev=fs[0]
    for (rid,v),f in zip(chain,fs[1:]):
        right=add(var(sq[11]),var(sq[12])) if f=='bundle' else var(f)
        need(rhs(rows[rid],v)==mul(var(prev),right),'old Horn product edge');prev=v
    protected=set(sq[:9]+sq[13:15]+[v for _,v in chain[:-1]])
    allowed={defs[v] for v in sq[:9]+sq[13:15]}|{rid for rid,_ in chain}
    for rid,p in enumerate(rows):
        need(rid in allowed or all(v not in protected for m in p for v in m),'Horn factor escapes')
    expected=copy.deepcopy(source);expected.pop('metrics',None)
    newrows=list(rows);changes=[]
    def rewrite(rid,p):
        changes.append({'row':rid,'old':terms(newrows[rid]),'new':terms(p)});newrows[rid]=p
    for v in sq[:9]+sq[13:15]:
        rewrite(defs[v],add(var(v),neg(roots[v])));expected['variables'][v]['kind']='gate'
    (r9,v9),(r10,v10),(r11,v11)=chain[8:]
    rewrite(r9,add(var(v9),neg(mul(var(chain[7][1]),var(sq[13])))))
    rewrite(r10,add(var(v10),neg(mul(var(v9),var(sq[14])))))
    rewrite(r11,add(var(v11),neg(mul(var(v10),var(v10)))))
    newroot=len(source['variables']);need(c['new_root']==newroot,'new Horn variable')
    expected['variables'].append({'name':'factored.horn','kind':'gate'})
    appended=add(var(newroot),neg(mul(var(v11),add(var(sq[11]),var(sq[12])))))
    need(poly(c['new_row'])==appended,'new Horn interface row')
    for rid,p in enumerate(list(newrows)):
        if rid not in {rid for rid,_ in chain} and any(v11 in m for m in p):rewrite(rid,substitute(p,v11,var(newroot)))
    # Bundle: square roots (c-a),(c-b) changed to one product h; G=h²-D².
    gvars=c['guard_variables'];h=gvars['h'];h2=gvars['old_second_square'];g=gvars['g'];dv=gvars['old_D_square']
    need(h==sq[9] and h2==sq[10],'bundle coordinate inventory')
    prs=[rid for rid,p in enumerate(newrows) if rhs(p,g)==mul(var(h),var(h2))]
    drs=[rid for rid,p in enumerate(newrows) if rhs(p,dv) is not None]
    need(len(prs)==len(drs)==1,'bundle old definitions');pr=prs[0];dr=drs[0];D2=rhs(newrows[dr],dv)
    need(roots[sq[11]] in (add(var(g),neg(var(dv))),add(var(dv),neg(var(g)))),'bundle square output interface')
    guard_allowed={defs[h],defs[h2],pr,dr,defs[sq[11]]}
    for rid,p in enumerate(newrows):need(rid in guard_allowed or all(v not in {h,h2,g,dv} for m in p for v in m),'bundle factor escapes')
    rewrite(defs[h],add(var(h),neg(mul(roots[h],roots[h2]))))
    rewrite(pr,add(var(g),neg(mul(var(h),var(h))),D2))
    rewrite(defs[sq[11]],add(var(sq[11]),neg(mul(var(g),var(g)))))
    deleted={defs[h2],dr};need(c['deleted_rows']==sorted(deleted),'factor row deletion inventory')
    need(c['changes']==changes,'factor exact rewrite ledger')
    expected['variables'][h]['kind']='gate'
    expected['residuals']=[dict(source['residuals'][rid],terms=terms(p)) for rid,p in enumerate(newrows) if rid not in deleted]+[{'label':'factored.horn','terms':terms(appended)}]
    expected['variant']+=':signed_factorization'
    need(expected==out,'factored literal mismatch')
    return out,{'horn_factor_roots':11,'all_original_square_roots_checked':17,'product_links_checked':11,'exact_row_rewrites':len(changes),'no_factor_escape':True}

def check_projection(source,cand):
    out=load(cand/'equation.json');cert=load(cand/'projection_certificate.json')
    need(cert['input_sha256']==digest(source) and cert['output_sha256']==digest(out),'projection hash')
    alias=cand/out.get('elimination',{}).get('certificate','projection_certificate.json')
    need(alias.is_file() and load(alias)==cert,'projection certificate metadata path or alias')
    rows={i:poly(x['terms']) for i,x in enumerate(source['residuals'])};live=set(range(len(source['variables'])));deleted=[]
    for s in cert['steps']:
        rid=s['row_id'];v=s['variable'];f=poly(s['restoration'])
        need(rid in rows and v in live and all(i in live-{v} for m in f for i in m),'projection acyclic live binding')
        need(rhs(rows[rid],v)==f,'nonmonic or wrong restoration')
        need(degree(f)<=2 and degree(f)==s['restoration_degree'],'restoration degree')
        need(s['name']==source['variables'][v]['name'] and s['kind']==source['variables'][v].get('kind'),'restoration variable metadata')
        rows={i:substitute(p,v,f) for i,p in rows.items() if i!=rid};rows={i:p for i,p in rows.items() if p}
        need(all(degree(p)<=2 for p in rows.values()),'projection degree exceeded')
        live.remove(v);deleted.append(v)
    retained=sorted({v for p in rows.values() for m in p for v in m});free=sorted(live-set(retained))
    need(retained==cert['retained_original_variables'] and sorted(rows)==cert['retained_original_rows'] and free==cert['unconstrained_removed'],'projection endpoint partitions')
    remap={v:i for i,v in enumerate(retained)}
    rr=[{'label':source['residuals'][rid]['label'],'terms':[[c,[remap[v] for v in m]] for m,c in sorted(p.items())]} for rid,p in sorted(rows.items())]
    need(out['variables']==[source['variables'][v] for v in retained] and out['residuals']==rr,'projection literal endpoint')
    need(out['domain']=='unrestricted integers','projection domain')
    expansion={}
    for row in rr:
        p=poly(row['terms']);expansion=add(expansion,mul(p,p))
    stored=load(cand/'expanded_polynomial.json')
    need(stored['terms']==terms(expansion),'full collected expansion mismatch')
    need(stored['variables']==len(retained),'expansion variable count')
    need(stored['domain']=='unrestricted integers' and stored['schema']=='sparse_integer_polynomial_v1','expanded polynomial metadata')
    metrics={'variables':len(retained),'rows':len(rr),'degree':degree(expansion),'monomials':len(expansion),'height':max(map(abs,expansion.values())),
             'row_height':max(abs(c) for r in rr for c,m in r['terms']),'projection_steps':len(deleted),'free_coordinates':free}
    declared=out['metrics']
    for actual,key in [('variables','variables'),('rows','quadratic_rows'),('degree','exact_degree'),('monomials','expanded_monomials'),('height','max_abs_expanded_coefficient'),('row_height','max_abs_row_coefficient')]:need(metrics[actual]==declared[key],'wrong endpoint metric '+key)
    # 12 deterministic evaluations at signed integer tuples test file interpretation,
    # not zero-existence. The coefficient equality above is the actual certificate.
    for seed in range(12):
        values=[((seed+7)*(i+11)*(i+3)%17)-8 for i in range(len(retained))]
        need(evalpoly(expansion,values)==sum(evalpoly(poly(r['terms']),values)**2 for r in rr),'sum-square evaluation')
    return metrics


PARENT_SHA='af0086e4133239359eb1a69888e1a122394f587bf50d81ebfdbb64982117b8ff'

def check_raw(parent,raw,c,odd):
    need(digest(parent)==PARENT_SHA,'frozen independently reviewed parent pin')
    need(c['parent_sha256']==PARENT_SHA,'cap parent pin')
    need(c['odd_auxiliary'] is odd,'variant flag')
    need(len(parent['variables'])==700 and len(parent['residuals'])==519,'parent dimensions')
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    A=names['shared.A'];W=names['shared.W']
    need(c['A']==A and c['W']==W and poly(c['cap_index'])=={(W,):2},'cap parameter binding')
    seedrows=[(j,r) for j,r in enumerate(parent['residuals']) if r['label'].endswith('.index_at_most_Y')]
    need(len(seedrows)==16,'sixteen principal indices')
    seeds=[];remove_labels={'shared_index.norm','shared_index.B_mod_U','shared_index.V_positive_product'}
    guardvars={names['shared_index.q4minus1'],names['shared_index.Vquotient_minus1']}
    for rid,row in seedrows:
        prefix=row['label'].split('.')[0];y=names[prefix+'.Y'];gap=names[prefix+'.YminusK']
        exponent=add(var(y),neg(var(gap)),neg(poly(row['terms'])))
        need(degree(exponent)<=1,'seed index is not affine')
        seeds.append({'row':rid,'Y':y,'slack':gap,'exponent':terms(exponent)})
        guardvars.add(gap)
        remove_labels.update(prefix+'.'+tail for tail in ['index_at_most_Y','norm3','S_mod_U','R_mod_4Y'])
    remove_labels.update('nonnegative.'+str(v) for v in guardvars)
    need(len(remove_labels)==85,'deletion label inventory')
    removed=[{'row':j,'literal':row} for j,row in enumerate(parent['residuals']) if row['label'] in remove_labels]
    need(len(removed)==85,'deletion exact cardinality')
    retained=[j for j,row in enumerate(parent['residuals']) if row['label'] not in remove_labels]
    need(c['parent_rows_removed']==removed,'strict deleted-row inventory')
    need(c['parent_rows_retained']==retained,'strict retained-row inventory')
    need(len(c['seed_indices'])==16,'seed certificate cardinality')
    for actual,expected in zip(c['seed_indices'],seeds):
        need({k:actual[k] for k in expected}==expected,'seed literal extraction')
    # All retained source rows must survive unchanged and in original order.
    nr=len(retained);n=len(parent['variables'])
    need(raw['residuals'][:nr]==[parent['residuals'][i] for i in retained],'retained raw literal rows')
    need(raw['variables'][:n]==parent['variables'],'retained raw variable declarations')
    core=['U','V','H','J','B','S','R','d','e','f','g','h','slack','Q','AV','AJ','BR','VV']
    ix={name:n+i for i,name in enumerate(core)}
    need(c['cap_variables']=={k:ix[k] for k in core[:14]},'cap coordinate inventory')
    newvars=[{'name':'cap.'+k,'kind':'signed_cap'} for k in core]
    guardkeys=['slack'] if odd else ['slack','e'];guards={}
    for k in guardkeys:
        gs=list(range(n+len(newvars),n+len(newvars)+3));guards[k]=gs
        newvars += [{'name':f'cap.nonnegative.{ix[k]}.{z}','kind':'signed_cap'} for z in 'abc']
    need(c['cap_guard_witnesses']==guards,'exact cap guards, including odd-factor guard absence')
    need(raw['variables'][n:]==newvars,'exact cap variable append inventory')
    v=lambda k:var(ix[k]);one={():1}
    rr=[]
    def row(label,p):rr.append({'label':'cap.'+label,'terms':terms(p)})
    for k,l,r in [('AV',var(A),v('V')),('AJ',var(A),v('J')),('BR',v('B'),v('R')),('VV',v('V'),v('V'))]:row(k,add(v(k),neg(mul(l,r))))
    for label,x,y,xy in [('norm','U','V','AV'),('auxiliary_norm','H','J','AJ'),('comparison_norm','S','R','BR')]:row(label,add(mul(v(x),v(x)),mul(v(y),v(y)),neg(mul(v(xy),v(xy))),neg(one)))
    row('comparison_progression',add(v('B'),neg(one),neg(mul({():4},mul(v('V'),v('d'))))))
    row('auxiliary_divisibility',add(v('J'),neg(mul(v('VV'),add(one,mul({():2 if odd else 1},v('e')))))))
    row('comparison_base',add(v('B'),neg(var(A)),neg(mul(v('H'),v('f')))))
    row('comparison_abscissa',add(v('S'),neg(v('U')),neg(mul(v('H'),v('g')))))
    row('comparison_ordinate',add(v('R'),{(W,):-2},neg(mul({():4},mul(v('V'),v('h'))))))
    row('squared_aggregate',add(v('V'),neg(one),{(W,):-2},neg(v('slack')),*[neg(mul(var(s['Y']),var(s['Y']))) for s in seeds]))
    differences=[add(var(s['Y']),neg(poly(s['exponent']))) for s in seeds]
    row('pooled_index_residue',add(*[mul(d,d) for d in differences],neg(mul(add(var(A),neg(one)),v('Q')))))
    for k in guardkeys:
        a,b,z=guards[k];row('nonnegative.'+str(ix[k]),add(v(k),{(a,a):-1,(b,b):-1,(z,z):-1,(z,):-1}))
    need(raw['residuals'][nr:]==rr,'exact cap row append inventory and formulas')
    expected=copy.deepcopy(parent);expected['variables']+=newvars;expected['residuals']=[parent['residuals'][i] for i in retained]+rr
    expected['variant']='direct_signed_pooled_squared_cap'
    need(raw==expected,'raw complete object equality')
    return {'parent_sha256':PARENT_SHA,'parent_variables':700,'parent_rows':519,'deleted_rows':85,'retained_rows':434,'seed_indices':16,'cap_rows':len(rr),'cap_new_variables':len(newvars),'cap_guard_triples':len(guards),'odd_auxiliary_guard_absent':odd,'raw_variables':len(raw['variables']),'raw_rows':len(raw['residuals'])}

def run(package,candidate):
    odd=candidate.name=='odd_cap';parent=load(package/'source/parent_source.json');raw=load(candidate/'raw_equation.json');c=load(candidate/'cap_certificate.json')
    raw_report=check_raw(parent,raw,c,odd)
    factored,factor_report=check_factor(raw,candidate)
    need(factor_report['exact_row_rewrites']==18,'Horn rewrite exact cardinality')
    need(load(candidate/'terminal_elimination_certificate.json')==load(candidate/'projection_certificate.json'),'projection certificate aliases')
    metrics=check_projection(factored,candidate)
    expected=(352,219,9355) if odd else (355,220,9370)
    need((metrics['variables'],metrics['rows'],metrics['monomials'])==expected,'frozen endpoint census')
    need(metrics['projection_steps']==229 and len(metrics['free_coordinates'])==141,'restoration/free census')
    return {'status':'PASS','candidate':candidate.name,'equation_sha256':digest(load(candidate/'equation.json')),'raw_cap':raw_report,'horn_factorization':factor_report,'metrics':metrics}

# Mutants use an in-memory file reader, never a producer checker. Relevant
# hashes are refreshed where necessary to reach semantic replay checks.
def mutation_controls(package,candidate):
    files={p.name:load(p) for p in candidate.glob('*.json')}
    parent=load(package/'source/parent_source.json');odd=candidate.name=='odd_cap';results=[]
    original_load=load
    def one(name,edit,stage):
        data=copy.deepcopy(files);source=copy.deepcopy(data['raw_equation.json']);edit(data,source)
        if stage=='projection':data['terminal_elimination_certificate.json']=copy.deepcopy(data['projection_certificate.json'])
        def fake_load(p):
            p=Path(p)
            return data[p.name] if p.parent==candidate and p.name in data else original_load(p)
        globals()['load']=fake_load
        try:
            if stage=='raw':check_raw(parent,data['raw_equation.json'],data['cap_certificate.json'],odd)
            elif stage=='factor':check_factor(source,candidate)
            elif stage=='projection':check_projection(data['factored_source.json'],candidate)
            else:raise RuntimeError('unknown mutation stage')
        except ValueError as e:results.append({'name':name,'status':'REJECTED','reason':str(e)})
        else:raise ValueError('mutation accepted: '+name)
        finally:globals()['load']=original_load
    def rowedit(d,label):return next(r for r in d['raw_equation.json']['residuals'] if r['label']==label)
    one('remove_retained_semantic_row',lambda d,s:d['raw_equation.json']['residuals'].pop(0),'raw')
    one('drop_deleted_row_inventory_entry',lambda d,s:d['cap_certificate.json']['parent_rows_removed'].pop(),'raw')
    one('drop_retained_row_inventory_entry',lambda d,s:d['cap_certificate.json']['parent_rows_retained'].pop(),'raw')
    one('change_cap_index',lambda d,s:d['cap_certificate.json']['cap_index'][0].__setitem__(0,3),'raw')
    one('change_seed_exponent',lambda d,s:d['cap_certificate.json']['seed_indices'][0]['exponent'][0].__setitem__(0,17),'raw')
    one('omit_cap_norm_constant',lambda d,s:rowedit(d,'cap.norm')['terms'].pop(0),'raw')
    one('corrupt_odd_or_positive_auxiliary_factor',lambda d,s:rowedit(d,'cap.auxiliary_divisibility')['terms'][1].__setitem__(0,-3),'raw')
    one('remove_aggregate_seed_square',lambda d,s:rowedit(d,'cap.squared_aggregate')['terms'].pop(2),'raw')
    one('corrupt_pooled_residue',lambda d,s:rowedit(d,'cap.pooled_index_residue')['terms'][0].__setitem__(0,781),'raw')
    one('append_unreported_cap_guard',lambda d,s:d['raw_equation.json']['residuals'].append(copy.deepcopy(d['raw_equation.json']['residuals'][-1])),'raw')
    one('corrupt_factor_square_root',lambda d,s:next(iter(d['factorization_certificate.json']['square_roots'].values()))[0].__setitem__(0,91),'factor')
    one('corrupt_Horn_product_edge',lambda d,s:d['factorization_certificate.json']['product_chain'][0].__setitem__(0,0),'factor')
    one('omit_factor_rewrite',lambda d,s:d['factorization_certificate.json']['changes'].pop(),'factor')
    def factendpoint(d,s):
        d['factored_source.json']['residuals'][0]['terms'][0][0]+=1
        d['factorization_certificate.json']['output_sha256']=digest(d['factored_source.json'])
    one('factor_endpoint_corruption_with_refreshed_hash',factendpoint,'factor')
    def escape(d,s):
        protected=d['factorization_certificate.json']['square_variables'][0]
        s['residuals'][0]['terms']=terms(add(poly(s['residuals'][0]['terms']),var(protected)))
        d['factorization_certificate.json']['input_sha256']=digest(s)
    one('Horn_protected_coordinate_escape_with_refreshed_hash',escape,'factor')
    one('corrupt_monic_restoration',lambda d,s:d['projection_certificate.json']['steps'][0]['restoration'][0].__setitem__(0,10),'projection')
    def cycle(d,s):
        st=d['projection_certificate.json']['steps'][0];st['restoration'].append([1,[st['variable']]])
    one('cyclic_restoration',cycle,'projection')
    one('drop_retained_coordinate_partition',lambda d,s:d['projection_certificate.json']['retained_original_variables'].pop(),'projection')
    one('expanded_coefficient_corruption',lambda d,s:d['expanded_polynomial.json']['terms'][0].__setitem__(0,d['expanded_polynomial.json']['terms'][0][0]+1),'projection')
    return results

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    report={'status':'PASS','independence':'Standard library only; no producer imports. Polynomial/Horn/projection kernel copied from the independently reviewed wave15 checker; fresh cap inventory/formula checker.','scope':'Finite literal source-to-quartic audit. The unbounded arithmetic and incoming C222/ZFC calibration remain ordinary proof dependencies.','variants':[]}
    for name in ['signed_cap','odd_cap']:
        candidate=args.package/name;result=run(args.package,candidate);result['mutation_controls']=mutation_controls(args.package,candidate);report['variants'].append(result);print(name,'PASS',result['metrics']['variables'],'variables;',len(result['mutation_controls']),'mutants rejected',flush=True)
    report['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (args.output/'INDEPENDENT_CAP_REPLAY.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Receipt:',args.output/'INDEPENDENT_CAP_REPLAY.json')
