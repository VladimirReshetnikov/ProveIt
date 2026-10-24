#!/usr/bin/env python3
"""Independent finite checker: no producer imports, standard library only.
Checks the new sign-guard transformation, pre-power dependency DAG,
Horn circuit equivalence, monic integer projection, and full quartic expansion.
The unbounded arithmetic implications are proved in REVIEW.md, not by testing.
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
def check_pairs(base,cand,squared):
    mixed=load(source_dir(base)/'mixed_source.json')
    dom=load(source_dir(base)/'domain_certificate.json')
    need(digest(mixed)=='67cd7a66c7fd09f0080e84f137d81339cb8d4bc7bdf0ff0ecc7a9cc5a6c39690','frozen baseline source pin')
    need(digest(dom)=='4cb7b950b007258ab38f542815610218a38f7c741e514ae3273a67ad6b1dab92','frozen baseline domain pin')
    e=load(cand/'paired_source.json');cert=load(cand/'pair_certificate.json')
    names={v['name']:i for i,v in enumerate(mixed['variables'])}
    pairs=[(names[f'choose{i}.remainder'],names[f'choose{i}.rslack']) for i in range(2)]+[(names[f'range{i}.remainder'],names[f'range{i}.slack']) for i in range(10)]
    baseline=copy.deepcopy(mixed)
    if 'original_source_sha256' in cert:need(cert['original_source_sha256']==digest(baseline),'original source pin in pair certificate')
    if squared:
        F=names['fact0.output'];S=names['mul.36']
        need(poly(mixed['residuals'][12]['terms'])==add(var(S),neg(mul(var(F),var(F)))),'F square definition')
        changes=[]
        for rid in (1,8,11):
            old=copy.deepcopy(mixed['residuals'][rid]);mixed['residuals'][rid]['terms']=terms(substitute(poly(old['terms']),F,var(S)))
            changes.append({'row':rid,'old':old,'new':copy.deepcopy(mixed['residuals'][rid])})
        need(cert['squared_factorial_carrier_changes']==changes,'squared source edit ledger')
        mixed['variant']+=':squared_factorial_carrier'
    need(digest(mixed)==cert['source_sha256'],'paired source input hash')
    n=len(mixed['variables']);r=len(mixed['residuals'])
    need(e['variables'][:n]==mixed['variables'],'source variables changed')
    need(e['residuals'][:r]==mixed['residuals'],'unreported source row changes')
    guardset=set(dom['guard_indices'])-({names['fact0.output']} if squared else set())
    removed={v for pair in pairs for v in pair};keep=sorted(guardset-removed)
    need(len(removed)==24 and len(pairs)==12,'wrong pair inventory')
    need(cert['original_guard_indices']==sorted(guardset),'input sign inventory')
    need(cert['retained_single_guards']==keep,'retained sign inventory')
    need([(p['left'],p['right']) for p in cert['pairs']]==pairs,'pair inventory')
    expectedrows=[];expectedvars=[]
    for v in keep:
        a=n+len(expectedvars);b=a+1;c=a+2
        expectedvars += [{'name':f'nonnegative.{v}.{z}','kind':'integer_guard'} for z in ('a','b','c')]
        expectedrows.append({'label':f'nonnegative.{v}','terms':terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    for j,(l,h) in enumerate(pairs):
        a=n+len(expectedvars);b=a+1;c=a+2
        expectedvars += [{'name':f'pairguard.{j}.{z}','kind':'integer_guard'} for z in ('a','b','c')]
        expectedrows.append({'label':f'pairguard.{j}','terms':terms({tuple(sorted((l,h))):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
        pc=cert['pairs'][j];out=pc['positive_power_output'];sumrow=pc['sum_row']
        need(poly(mixed['residuals'][sumrow]['terms'])=={():-1,(out,):1,(l,):-1,(h,):-1},'bad pair sum row')
        need(pc['guard_variables']==[a,b,c] and pc['guard_row']==r+len(expectedrows)-1,'pair witness row binding')
        need(mixed['variables'][out]['name'] in ('pow4.output','pow7.output','pow12.output','pow15.output'),'unproved pair total')
    need(e['variables'][n:]==expectedvars,'new guard variable declarations')
    need(e['residuals'][r:]==expectedrows,'new guard rows')
    # Check actual pre-semantic square shell, and all 57 power ports are included.
    budget=dom['square_budget'];W=budget['frame_variable'];atoms=[poly(x['affine']) for x in budget['atoms']]
    frame=add(var(W),{():-2},*[neg(mul(a,a)) for a in atoms])
    need(frame==poly(mixed['residuals'][budget['frame_row']]['terms']),'square budget identity')
    for pc in budget['power_calls']:
        for role in ('base','exponent','output'):
            need(poly(pc[role]) in atoms,'power port absent from square budget')
    # No removed guard is supplied to this lower-bound engine.
    bounds,steps=closure([poly(x['terms']) for x in mixed['residuals']],dict.fromkeys(keep,0)|{W:2})
    essential={'choose0.output':1,'mul.400':2,'mul.2':0,'mul.36':0,'y':1,'add.34':1,
               'shared_index.V':1,'mul.469':4}
    for name,b in essential.items(): need(bounds.get(names[name],-1)>=b,'presemantic bound missing: '+name)
    for v in keep:
        if mixed['variables'][v]['name'].endswith('.YminusK'):
            yy=names[mixed['variables'][v]['name'].replace('.YminusK','.Y')]
            need(bounds.get(yy,-1)>=1,'nonpositive presemantic index ordinate')
    need(all(lower(poly(pc['exponent']),bounds)>=1 for pc in budget['power_calls']),'presemantic exponent not positive')
    if squared: need(names['fact0.output'] not in bounds,'F sign derived prematurely')
    # Signed-power orientation order: q^t, (rho+1)^t, then F>=1,
    # B>=1 from B*i=C+F²+1, B^K potentially -1, (N+V+1)^K orients K.
    t0=names['t0'];q=names['mul.400'];F=names['fact0.output'];D=names['choose0.output'];V=names['pow0.output'];u=names['fact0.remainder'];v=names['fact0.slack'];FF=names['mul.6']
    need(poly(mixed['residuals'][2]['terms'])==add(var(FF),neg(mul(var(F),var(D)))),'DF gate')
    need(poly(mixed['residuals'][3]['terms'])==add(var(D),var(V),neg(var(u)),neg(var(FF)),{():-1}),'factorial ceiling')
    need(poly(mixed['residuals'][4]['terms'])==add(var(D),neg(var(u)),neg(var(v)),{():-1}),'factorial remainder')
    neededpow={4:({'base':var(q),'exponent':{():16,(t0,):1}}),0:({'base':{():1,(names['mul.2'],):1},'exponent':{():16,(t0,):1}})}
    for j,pp in neededpow.items():
        for role,p in pp.items():need(poly(budget['power_calls'][j][role])==p,'orientation call changed')
    restored_guards=set(keep)|removed|({F} if squared else set())
    need(restored_guards==set(dom['guard_indices']),'not all original guards restored')
    need((cand/'presemantic_certificate.json').is_file(),'missing fresh presemantic certificate')
    producer_pre=check_presemantic_certificate(mixed,keep,cand)
    return e,{'producer_presemantic_certificate':producer_pre,'single_guards':len(keep),'pair_guards':12,'input_base_rows':r,'input_base_variables':n,
              'presemantic_bound_steps':len(steps),'presemantic_essential_bounds':{name:bounds[names[name]] for name in essential},
              'presemantic_derived_guard_signs':sorted(set(bounds)&removed),'removed_pair_guards':sorted(removed),
              'all_original_guards_restored':True,'squared_radius':squared},steps

def check_presemantic_certificate(mixed,keep,cand):
    c=load(cand/'presemantic_certificate.json');need(c['guarded_leaves']==keep,'producer presemantic initial leaves')
    bounds=dict.fromkeys(keep,0);rows=[poly(r['terms']) for r in mixed['residuals']]
    def lb(p):
        total=0;deps={}
        for m,a in p.items():
            if not m:total+=a;continue
            need(a>=0,'negative monotonic coefficient in presemantic certificate')
            z=a
            for v,k in Counter(m).items():
                if v in bounds:deps[v]=bounds[v];z*=bounds[v]**k
                else:need(k%2==0,'unproved presemantic odd-power leaf');z=0
            total+=z
        return total,[[v,b] for v,b in sorted(deps.items())]
    for step in c['steps']:
        v=step['variable'];need(v not in bounds,'repeated presemantic variable')
        f=poly(step['restoration']);need(rhs(rows[step['row']],v)==f,'presemantic row restoration')
        value,deps=lb(f);need(step['lower_bound']==min(64,value) and value>=0,'presemantic lower bound arithmetic')
        need(step['dependencies']==deps,'presemantic dependency binding');bounds[v]=step['lower_bound']
    expectedrids=[i for i,r in enumerate(mixed['residuals']) if r['label'].endswith('.index_at_most_Y')]
    need([s['row'] for s in c['seed_indices']]==expectedrids,'presemantic complete seed coverage')
    for seed in c['seed_indices']:
        y=seed['Y'];e=seed['slack'];ex=poly(seed['exponent'])
        need(e in keep and rows[seed['row']]==add(var(y),neg(var(e)),neg(ex)),'presemantic seed row')
        value,_=lb(ex);need(value==seed['exponent_lower_bound'] and value>=1,'presemantic exponent positivity')
        need(bounds.get(y,0)>=1,'presemantic Y positivity')
    return {'status':'PASS','steps':len(c['steps']),'positive_seed_indices':len(expectedrids)}

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

def negative_controls(base,cand,squared):
    outcomes=[]
    # General lemma hypotheses are individually necessary; these are actual
    # integer witnesses for the weakened small interfaces.
    need((-1)*(-1)==1 and -1+-1<0,'negative-sum counterexample')
    outcomes.append({'name':'omit_nonnegative_sum','r':-1,'s':-1,'a':1,'b':0,'c':0,'product_guard_satisfied':True,'individual_signs_fail':True})
    need(-1+2>=0 and -1*2<0,'missing-product counterexample')
    outcomes.append({'name':'omit_product_guard','r':-1,'s':2,'sum_nonnegative':True,'individual_signs_fail':True})
    # Small exhaustive equivalence and universal-form coverage, not an unbounded proof.
    sums={a*a+b*b+c*(c+1) for a in range(17) for b in range(17) for c in range(17)}
    need(all(n in sums for n in range(257)),'three-square coverage fixture')
    cases=0
    for r in range(-20,21):
        for s in range(-20,21):
            need(((r+s>=0 and r*s>=0)==(r>=0 and s>=0)),'pair lemma finite fixture');cases+=1
    return outcomes,{'three_square_coverage':257,'pair_cases':cases}

def run(base,cand,squared):
    e,pairs,steps=check_pairs(base,cand,squared)
    factored,factors=check_factor(e,cand)
    metrics=check_projection(factored,cand)
    nc,fixtures=negative_controls(base,cand,squared)
    return {'status':'PASS','scope':'finite certificate replay and local mathematical audit; complete incoming literal-source/C222 calibration and simultaneous signed-Pell theorem are imported, not independently certified here' ,
            'candidate':str(cand),'candidate_equation_sha256':digest(load(cand/'equation.json')),'pair_transform':pairs,
            'horn_factorization':factors,'metrics':metrics,'negative_controls':nc,'finite_fixtures':fixtures},steps

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--baseline',required=True,type=Path);ap.add_argument('--candidate',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--squared-radius',action='store_true');a=ap.parse_args()
    receipt,steps=run(a.baseline,a.candidate,a.squared_radius);a.output.mkdir(parents=True,exist_ok=True)
    (a.output/'INDEPENDENT_REPLAY.json').write_text(json.dumps(receipt,indent=2)+'\n');(a.output/'PRESEMANTIC_BOUNDS.json').write_text(json.dumps(steps,indent=2)+'\n');print(json.dumps(receipt,indent=2))
