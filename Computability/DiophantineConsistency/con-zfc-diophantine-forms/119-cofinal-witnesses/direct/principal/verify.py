#!/usr/bin/env python3
"""Independent exact checker for the signed-factorial quartic.

No builder, optimizer, symbolic algebra package, or network is imported.
Finite algebra is checked here; the quantified theorem is in PROOF.md.
"""
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations_with_replacement
import argparse, copy, hashlib, json

HERE=Path(__file__).resolve().parent

def need(ok,why):
    if not ok:raise ValueError(why)

def enc(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(x):return hashlib.sha256(enc(x)).hexdigest()
def norm(ts):
    z=Counter()
    for c,m in ts:z[tuple(sorted(m))]+=c
    return {m:c for m,c in z.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def add(*ps):
    z=Counter()
    for p in ps:
        for m,c in p.items():z[m]+=c
    return {m:c for m,c in z.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def var(i):return {(i,):1}
def mul(p,q):
    z=Counter()
    for m,c in p.items():
        for n,d in q.items():z[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in z.items() if c}
def sub(p,v,q):
    z={}
    for m,c in p.items():
        a={():c}
        for w in m:a=mul(a,q if w==v else var(w))
        z=add(z,a)
    return z
def deg(p):return max(map(len,p),default=0)
def solved(p,v):
    c=p.get((v,),0)
    if abs(c)!=1:return None
    q={m:-c*a for m,a in p.items() if m!=(v,)}
    return None if any(v in m for m in q) else q

def source_check(parent,child,cert):
    need(sha(parent)==cert['input_sha256'] and sha(child)==cert['output_sha256'],'source hashes')
    need((len(parent['variables']),len(parent['residuals']))==(739,532),'parent dimensions')
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    removed=sorted(names[f'nonnegative.{i}.{s}'] for i in [0,3,12] for s in 'abc')
    retained=[i for i in range(739) if i not in removed]+[739]
    need(retained==cert['retained_old_coordinates'] and removed==cert['removed_old_coordinates'],'source coordinate map')
    need(cert['appended_old_index']==739,'new square index')
    remap={v:i for i,v in enumerate(retained)}
    replacements={1:{(5,):1,(4,27):-1},
      11:{(26,):1,():-18,(0,):-1,(1,):-1,(2,):-1,(27,):-1},
      469:{(0,):1,(739,739):-1},474:{(2,):1,(7,7):-1,(7,):1}}
    old_expected={1:{(5,):1,(3,4):-1},11:{(26,):1,():-18,(0,):-1,(1,):-1,(2,):-1,(3,):-1}}
    for i,p in old_expected.items():need(norm(parent['residuals'][i]['terms'])==p,'old structural row')
    newrows=[]
    for i,r in enumerate(parent['residuals']):
        p=norm(r['terms'])
        if i in [469,471,474]:need(r['label']=='nonnegative.'+str({469:0,471:3,474:12}[i]),'old guard identity')
        else:need(not any(v in removed for m in p for v in m),'private guard coordinates')
        if i==471:continue
        q=replacements.get(i,p)
        label={469:'cofinal.horizon_square',474:'cofinal.signed_factorial_beta_modulus'}.get(i,r['label'])
        newrows.append({'label':label,'terms':[[c,[remap[v] for v in m]] for m,c in sorted(q.items())]})
    need(child['residuals']==newrows,'all transformed source rows')
    vs=parent['variables']+[{'name':'cofinal.horizon_root','kind':'integer_square'}]
    need(child['variables']==[vs[v] for v in retained],'all source variable records')
    need(child['domain']=='unrestricted integers','signed source domain')
    return {'source_variables':len(child['variables']),'source_rows':len(newrows),'changed_or_removed_rows':[1,11,469,471,474]}

def factor_check(source,target,cert):
    need(sha(source)==cert['input_sha256'] and sha(target)==cert['output_sha256'],'factorization hashes')
    rows=[norm(r['terms']) for r in source['residuals']]
    names={v['name']:i for i,v in enumerate(source['variables'])}
    sq=[names['sqd.'+str(i)] for i in range(17)]
    need(sq==cert['square_variables'],'all original square ports')
    defs={};roots={}
    for s in sq:
        hits=[i for i,r in enumerate(source['residuals']) if r['label']=='nonnegative_square_difference' and rows[i].get((s,))==1 and solved(rows[i],s) is not None]
        need(len(hits)==1,'unique original square definition');defs[s]=hits[0]
        root=norm(cert['square_roots'][str(s)])
        need(deg(root)<=1 and mul(root,root)==solved(rows[defs[s]],s),'exact affine square root')
        roots[s]=root
    chain=cert['product_chain'];need(len(chain)==11,'eleven product links')
    previous=sq[0]
    factors=sq[1:9]+['bundle',sq[13],sq[14]]
    for (rid,out),f in zip(chain,factors):
        rhs=mul(var(previous),add(var(sq[11]),var(sq[12])) if f=='bundle' else var(f))
        need(solved(rows[rid],out)==rhs,'original Horn product link');previous=out
    protected=set(sq[:9]+sq[13:15]+[v for r,v in chain[:-1]])
    allowed=set(defs[s] for s in sq[:9]+sq[13:15])|{r for r,v in chain}
    need(all(not any(v in protected for m in p for v in m) for i,p in enumerate(rows) if i not in allowed),'no escaping ordinary factors')
    expected=list(rows);variables=copy.deepcopy(source['variables'])
    for s in sq[:9]+sq[13:15]:
        expected[defs[s]]=add(var(s),neg(roots[s]));variables[s]['kind']='gate'
    r9,o9=chain[8];r10,o10=chain[9];r11,o11=chain[10]
    expected[r9]=add(var(o9),neg(mul(var(chain[7][1]),var(sq[13]))))
    expected[r10]=add(var(o10),neg(mul(var(o9),var(sq[14]))))
    expected[r11]=add(var(o11),neg(mul(var(o10),var(o10))))
    newroot=len(variables);need(cert['new_root']==newroot,'factored Horn output index')
    variables.append({'name':'factored.horn','kind':'gate'})
    for i,p in enumerate(expected):
        if i not in {r for r,v in chain} and any(o11 in m for m in p):expected[i]=sub(p,o11,var(newroot))
    newrow=add(var(newroot),neg(mul(var(o11),add(var(sq[11]),var(sq[12])))))
    need(norm(cert['new_row'])==newrow,'final nonnegative Horn multiplication')
    gv=cert['guard_variables'];h,unused,g,dv=[gv[k] for k in ['h','old_second_square','g','old_D_square']]
    need(h==sq[9] and unused==sq[10],'bundle root ports')
    prs=[i for i,p in enumerate(rows) if solved(p,g)==mul(var(h),var(unused))]
    drs=[i for i,p in enumerate(rows) if solved(p,dv) is not None]
    need(len(prs)==len(drs)==1,'bundle intermediate definitions')
    pr,dr=prs[0],drs[0];D2=solved(rows[dr],dv)
    need(mul(roots[sq[11]],roots[sq[11]])==solved(rows[defs[sq[11]]],sq[11]),'original bundle difference square')
    need(roots[sq[11]] in [add(var(g),neg(var(dv))),add(var(dv),neg(var(g)))],'bundle root difference')
    guardallowed={defs[h],defs[unused],pr,dr,defs[sq[11]]}
    need(all(not any(v in {h,unused,g,dv} for m in p for v in m) for i,p in enumerate(rows) if i not in guardallowed),'no escaping bundle intermediates')
    expected[defs[h]]=add(var(h),neg(mul(roots[h],roots[unused])))
    expected[pr]=add(var(g),neg(mul(var(h),var(h))),D2)
    expected[defs[sq[11]]]=add(var(sq[11]),neg(mul(var(g),var(g))))
    variables[h]['kind']='gate'
    deleted={defs[unused],dr};need(sorted(deleted)==cert['deleted_rows'],'only redundant bundle rows deleted')
    result=[{'label':r['label'],'terms':terms(expected[i])} for i,r in enumerate(source['residuals']) if i not in deleted]
    result.append({'label':'factored.horn','terms':terms(newrow)})
    need(result==target['residuals'] and variables==target['variables'],'complete independent factorization reconstruction')
    return {'exact_affine_roots':17,'horn_product_links':11,'removed_redundant_bundle_rows':2}

def projection_check(source,target,cert):
    need(sha(source)==cert['input_sha256'] and sha(target)==cert['output_sha256'],'projection hashes')
    rows={i:norm(r['terms']) for i,r in enumerate(source['residuals'])};deleted=set()
    for st in cert['steps']:
        rid,v=st['row_id'],st['variable'];q=norm(st['restoration'])
        need(rid in rows and v not in deleted,'projection target')
        need(not any(v in m or any(w in deleted for w in m) for m in q),'projection dependencies')
        need(deg(q)<=2,'restoration degree')
        needed=add(var(v),neg(q))
        need(rows[rid] in [needed,neg(needed)],'exact integral monic defining row')
        fresh={}
        for i,p in rows.items():
            if i==rid:continue
            pp=sub(p,v,q);need(deg(pp)<=2,'quadratic substitution preserved')
            if pp:fresh[i]=pp
        rows=fresh;deleted.add(v)
    retained=sorted({v for p in rows.values() for m in p for v in m})
    need(retained==cert['retained_original_variables'],'retained variables')
    need(sorted(rows)==cert['retained_original_rows'],'retained row list')
    need(sorted(set(range(len(source['variables'])))-set(retained)-deleted)==cert['unconstrained_removed'],'free coordinates restored as zero')
    rename={v:i for i,v in enumerate(retained)}
    expected=[{'label':source['residuals'][i]['label'],'terms':[[c,[rename[v] for v in m]] for m,c in sorted(p.items())]} for i,p in sorted(rows.items())]
    need(expected==target['residuals'],'entire projected polynomial system')
    need(target['variables']==[source['variables'][v] for v in retained],'projected variable records')
    return {'integral_restorations':len(deleted),'unconstrained_removed':len(cert['unconstrained_removed'])}

def translation_check(source,target,cert):
    need(sha(source)==cert['input_sha256'] and sha(target)==cert['output_sha256'],'translation hashes')
    shifts=cert['shifts'];need(len({i for i,s in shifts})==len(shifts),'unique translations')
    need(all(isinstance(s,int) for i,s in shifts),'integral translations')
    for before,after in zip(source['residuals'],target['residuals']):
        p=norm(before['terms'])
        for i,s in shifts:p=sub(p,i,{(i,):1,():s})
        need(p==norm(after['terms']) and before['label']==after['label'],'translated residual')
        for i,s in shifts:p=sub(p,i,{(i,):1,():-s})
        need(p==norm(before['terms']),'inverse integral translation')
    need(source['variables']==target['variables'],'translation variable identity')
    return {'translated_coordinates':len(shifts)}

def expansion_check(e,expanded,metrics):
    z=Counter()
    for row in e['residuals']:
        p=sorted(norm(row['terms']).items());need(max((len(m) for m,c in p),default=0)<=2,'quadratic final row')
        for i,j in combinations_with_replacement(range(len(p)),2):
            m,c=p[i];n,d=p[j];z[tuple(sorted(m+n))]+=(1 if i==j else 2)*c*d
    ts=terms({m:c for m,c in z.items() if c})
    need(expanded=={'schema':'sparse_integer_polynomial_v1','domain':'unrestricted integers','variables':len(e['variables']),'terms':ts},'every expanded coefficient')
    actual={'variables':len(e['variables']),'quadratic_rows':len(e['residuals']),'exact_degree':max(len(m) for c,m in ts),
            'expanded_monomials':len(ts),'max_abs_expanded_coefficient':max(abs(c) for c,m in ts),
            'max_abs_row_coefficient':max(abs(c) for r in e['residuals'] for c,m in r['terms'])}
    need(actual==metrics,'all final metrics');return actual

def arithmetic_bindings(source,raw,parent_raw,domain):
    # The signed-source coordinate map removes only auxiliary indices >549.
    rows=[norm(r['terms']) for r in source['residuals']]
    need(raw['powers']==parent_raw['powers'] and raw['seeds']==parent_raw['seeds'],'every actual power and seed port unchanged')
    changes={i for i,(a,b) in enumerate(zip(raw['rows'],parent_raw['rows'])) if a!=b}
    need(changes=={2,39},'exact two raw arithmetic definition changes')
    need(raw['rows'][2]['terms']==[[-1,[5,56]],[1,[6]]] and raw['rows'][39]['terms']==[[-1,[56]],[-1,[53]],[1,[54]]],'raw squared-radius and R definitions')
    need(rows[1]=={(5,):1,(4,27):-1} and rows[11]=={(26,):1,():-18,(0,):-1,(1,):-1,(2,):-1,(27,):-1},'mixed arithmetic definitions')
    # This exact identity supplies the only new presemantic y-sign premise.
    # If y is integral and 4y+1 is a square, then y>=0. No index recovery,
    # sign of F or V, or exceptional-zero argument is used.
    modulus=[p for p,r in zip(rows,source['residuals']) if r['label']=='cofinal.signed_factorial_beta_modulus']
    need(len(modulus)==1 and modulus[0]=={(2,):1,(7,7):-1,(7,):1},'literal consecutive-product modulus')
    consecutive_identity=add(mul(add(mul({():2},var(7)),{():-1}),add(mul({():2},var(7)),{():-1})),
                             mul({():-4},var(2)),{():-1})
    need(consecutive_identity==mul({():-4},modulus[0]),'square identity (2V-1)^2=4y+1')
    # Independently expand the bootstrap and the two local cuts.
    def cut(rid,replacements):
        p=rows[rid]
        for v,row in replacements:
            q=solved(rows[row],v);need(q is not None,'cut monic wire');p=sub(p,v,q)
        return p
    boot=cut(212,[(260,211),(259,210)])
    W,A,z=var(256),var(257),var(258)
    expected=add(mul(A,A),neg(mul(mul(mul(W,W),W),mul(add(W,{():2}),mul(add(z,{():1}),add(z,{():1}))))),{():-1})
    need(boot==expected,'bootstrap A^2-W^3(W+2)(z+1)^2-1')
    main=cut(220,[(273,219)])
    X,Y=var(268),var(269)
    need(main==add(mul(X,X),mul(Y,Y),neg(mul(mul(A,A),mul(Y,Y))),{():-1}),'main norm cut')
    power=cut(232,[(284,231),(283,230),(273,219),(279,229),(280,227),(281,228)])
    collapsed=sub(sub(power,5,{}),7,{})
    q=var(282)
    need(collapsed==add(X,neg(mul(add(A,{():-1}),add(Y,mul({():2},q))))),'zero-output/unit-base residue contradiction')
    # The all-square frame is recomputed from every distinct actual port.
    base_names={v['name']:i for i,v in enumerate(source['variables'][:550])}
    defs={r['gate']:norm(r['terms']) for r in raw['rows'] if r.get('gate') is not None}
    memo={}
    def atom(a):
        if a[0]=='c':return {():a[1]} if a[1] else {}
        v=a[1];name=raw['variables'][v]['name']
        if name in base_names:return var(base_names[name])
        if v in memo:return memo[v]
        need(v in defs,'raw atom definition');rhs=solved(defs[v],v);need(rhs is not None,'raw atom monicity')
        out={}
        for m,c in rhs.items():
            p={():c}
            for u in m:p=mul(p,atom(['v',u]))
            out=add(out,p)
        need(deg(out)<=1,'actual port affine binding');memo[v]=out;return out
    seen=set();atoms=[];frame={():2}
    for pw in raw['powers']:
        for role in ('base','exponent','output'):
            a=pw[role];key=tuple(a)
            if key in seen:continue
            seen.add(key);p=atom(a);atoms.append({'raw_token':a,'affine_mixed_terms':terms(p)});frame=add(frame,mul(p,p))
    need(rows[468]==add(var(256),neg(frame)),'complete all-square budget binding')
    # Exact gate-bound certificate for all changed seed exponents. The two
    # semantic leaves t0>=0 and y>=0 are proved in the ordinary bootstrap.
    rnames={v['name']:i for i,v in enumerate(raw['variables'])}
    leaves={rnames['t0']:0,rnames['x']:0,rnames['y']:0}
    for n,i in rnames.items():
        if n.startswith('crt.encoded'):leaves[i]=0
    lower_cache={};steps=[]
    def lower(a):
        if a[0]=='c':return a[1]
        v=a[1]
        if v in leaves:return leaves[v]
        if v in lower_cache:return lower_cache[v]
        need(v in defs,'seed lower-bound definition')
        rhs=solved(defs[v],v);need(rhs is not None and all(c>=0 for c in rhs.values()),'nonnegative seed constructor')
        total=0;deps={};signed_even=[]
        for m,c in rhs.items():
            value=c
            for u,k in Counter(m).items():
                if raw['variables'][u]['name']=='fact0.output':
                    need(k%2==0,'unproved signed factorial in seed');lb=0;signed_even.append([u,k])
                else:lb=lower(['v',u])
                need(lb>=0,'nonnegative factor');deps[u]=lb;value*=lb**k
            total+=value
        total=min(total,64);lower_cache[v]=total
        steps.append({'variable':v,'defining_terms':terms(defs[v]),'dependencies':[[u,b] for u,b in sorted(deps.items())],
                      'signed_even_powers':signed_even,'lower_bound':total})
        return total
    seeds=[]
    for s in raw['seeds']:
        lb=lower(s['exponent']);need(lb>=1,'positive actual seed exponent');seeds.append({'exponent':s['exponent'],'pair':s['pair'],'lower_bound':lb})
    return {'schema':'consecutive_modulus_presemantic_bindings_v1','raw_sha256':sha(raw),'source_sha256':sha(source),
            'all_square_frame_atoms':atoms,'raw_positive_seed_count':len(seeds),'seeds':seeds,'lower_bound_steps':steps,
            'leaf_bounds':[[i,b] for i,b in sorted(leaves.items())],
            'consecutive_modulus_identity':terms(consecutive_identity),
            'bootstrap_norm':terms(boot),'main_norm':terms(main),'power0_cut':terms(power),'collapsed_unit_base_cut':terms(collapsed),
            'ordinary_dependencies':['PROOF.md: t0 is a square','PROOF.md: V*(V-1)>=0 for every integer V','PROOF.md: y=V*(V-1), hence y+1>=1'],
            'norm_residue_cuts_are_diagnostics_for_initial_y_sign':True,
            'no_unproved_factorial_sign_in_seed_certificate':True}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=HERE);ap.add_argument('--output',type=Path);ap.add_argument('--emit-bindings',action='store_true');a=ap.parse_args()
    root=a.root;read=lambda n:json.loads((root/n).read_text())
    provenance=read('PROVENANCE.json')
    need(provenance['commit']=='45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6','frozen repository commit')
    for name,expected in provenance['parent_files_sha256'].items():
        need(hashlib.sha256((root/'parent'/name).read_bytes()).hexdigest()==expected,'frozen parent bytes '+name)
    need(hashlib.sha256((root/'source517.json').read_bytes()).hexdigest()==provenance['source517_original_sha256'],'literal final 517-variable comparison')
    parent=read('parent/direct/derived16_signed_shell/guarded.json');source=read('signed_source.json')
    receipt={'status':'PASS','source':source_check(parent,source,read('source_transformation.json'))}
    factored=read('factored_source.json');receipt['factorization']=factor_check(source,factored,read('factorization.json'))
    compact=read('untranslated_equation.json');receipt['projection']=projection_check(factored,compact,read('projection2.json'))
    final=read('equation.json');receipt['translation']=translation_check(compact,final,read('translation.json'))
    receipt['metrics']=expansion_check(final,read('expanded_polynomial.json'),read('METRICS.json'))
    binding=arithmetic_bindings(source,read('raw_audit_input.json'),read('parent/architecture/derived16_shell/raw/raw_audit_input.json'),read('parent/direct/derived16_signed_shell/domain_certificate.json'))
    if a.emit_bindings:(root/'SEED_AND_BOOTSTRAP_CERTIFICATE.json').write_bytes(enc(binding))
    else:need(binding==read('SEED_AND_BOOTSTRAP_CERTIFICATE.json'),'exact stored bootstrap and seed certificate')
    receipt['arithmetic_bindings']={'positive_seeds':binding['raw_positive_seed_count'],'square_frame_atoms':len(binding['all_square_frame_atoms']),
                                  'consecutive_product_square_identity':True,'checked_norm_residue_diagnostics':4,
                                  'exceptional_zero_exclusion_needed_for_y_sign':False}
    # Negative controls go through the independently checked coefficient map.
    wrong=copy.deepcopy(read('expanded_polynomial.json'));wrong['terms'][0][0]+=1
    try:expansion_check(final,wrong,read('METRICS.json'))
    except ValueError:pass
    else:raise ValueError('modified coefficient accepted')
    wrong=copy.deepcopy(source);wrong['residuals'][1]['terms'][0][0]-=1
    try:source_check(parent,wrong,read('source_transformation.json'))
    except ValueError:pass
    else:raise ValueError('modified radius accepted')
    receipt['corruptions_rejected']=2
    receipt['scope']='Full literal source change; independently reconstructed Horn and bundle factorization; all integral monic projections; two-way translations; every quartic coefficient; exact consecutive-product square identity; entire square budget; all seed bounds; norm/residue diagnostics. Quantified semantics is proved separately.'
    if a.output:a.output.write_bytes(enc(receipt))
    print(json.dumps(receipt,sort_keys=True))

if __name__=='__main__':main()
