#!/usr/bin/env python3
"""Independent signed graph, factorization, and integral projection audit."""
import argparse, collections, copy, hashlib, json
from pathlib import Path
from audit_literal_independent import collect,serial,mul,substitute,normrow,sos,metrics,need,read

def add(*ps):return collect((c,m) for p in ps for m,c in p.items())
def neg(p):return {m:-c for m,c in p.items()}
def var(v):return {(v,):1}
def const(c):return {():c} if c else {}
def filehash(o):return hashlib.sha256((json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
def restore(p,v):
    a=p.get((v,));need(a in [-1,1],'nonmonic definition')
    need(all(v not in m for m in p if m!=(v,)),'self definition')
    return {m:-a*c for m,c in p.items() if m!=(v,)}
def row_for(rows,v,label=None):
    out=[]
    for i,r in enumerate(rows):
        if label is not None and r['label']!=label:continue
        p=normrow(r)
        if p.get((v,)) in [-1,1] and all(v not in m for m in p if m!=(v,)):out.append(i)
    need(len(out)==1,'ambiguous definition '+str(v));return out[0]

def verify_positive_seeds_v2(meta,certificate,raw_eq,known):
    names={v['name']:i for i,v in enumerate(meta['variables'])};retained={v['name']:i for i,v in enumerate(raw_eq['variables'])};defs={int(v):meta['rows'][r] for v,r in meta['gates'].items()}
    need(not certificate['prior_carrier'] and 'M0' not in names,'v2 reviewer supports factorial carrier chart only')
    leaves={names[n]:0 for n in names if n in ('t0','x','fact0.output','endpoint.r0') or n.startswith('crt.encoded.') or n=='crt.encoded_index_minus_one'}
    for v in leaves:need(meta['variables'][v]['name'] in retained and retained[meta['variables'][v]['name']] in known,'unproved v2 natural leaf')
    leaves[names['y']]=1;need(sorted(leaves.items())==[tuple(x) for x in certificate['leaf_bounds']],'wrong v2 leaf floor')
    # Expand only the short endpoint addition chain to prove y=F+r0+1.
    def ep(v):
        if v not in defs:return var(v)
        rhs=restore(normrow(defs[v]),v);need(all(len(m)<=1 for m in rhs),'endpoint nonaffine')
        return substitute(rhs,{u:ep(u) for m in rhs for u in m})
    er=next(r for r in meta['rows'] if r['label']=='endpoint.first_remainder')
    e=substitute(normrow(er),{u:ep(u) for m in normrow(er) for u in m})
    want=add(var(names['y']),neg(var(names['fact0.output'])),neg(var(names['endpoint.r0'])),const(-1))
    need(e==want,'v2 endpoint floor premise')
    bounds=dict(leaves)
    for step in certificate['proof_steps']:
        v=step['variable'];need(v in defs and defs[v]==step['row'] and v not in bounds,'invalid v2 gate')
        rhs=restore(normrow(defs[v]),v);need(all(c>=0 for c in rhs.values()),'nonmonotone v2 gate')
        deps={u for m in rhs for u in m};need(deps<=bounds.keys(),'forward v2 dependency')
        need([[u,bounds[u]] for u in sorted(deps)]==step['dependencies'],'v2 dependency floor mismatch')
        total=0
        for m,c in rhs.items():
            for u in m:
                need(len(m)<=1 or bounds[u]>=0,'nonlinear negative floor');c*=bounds[u]
            total+=c
        need(step['lower_bound']==min(64,total),'wrong v2 lower bound');bounds[v]=step['lower_bound']
    need(len(meta['seeds'])==len(certificate['seeds']),'v2 seed count')
    for orig,s in zip(meta['seeds'],certificate['seeds']):
        need(orig['exponent']==s['exponent'] and orig['pair']==s['pair'],'v2 seed identity');typ,v=orig['exponent'];b=v if typ=='c' else bounds[v]
        need(s['lower_bound']==b and b>=1,'nonpositive v2 seed')
    return {'seed_count':len(meta['seeds']),'endpoint_identity_checked':True,'compositional_lower_bound_steps':len(certificate['proof_steps']),'all_leaves_proved_natural':True}

def verify_positive_seeds(meta,certificate,raw_eq,known):
    if certificate['schema']=='presemantic_positive_seed_indices_v2':return verify_positive_seeds_v2(meta,certificate,raw_eq,known)
    names={v['name']:i for i,v in enumerate(meta['variables'])}; retained={v['name']:i for i,v in enumerate(raw_eq['variables'])}
    defs={int(v):meta['rows'][r] for v,r in meta['gates'].items()}; prior='M0' in names; fresh=len(meta['variables'])
    need(certificate['prior_carrier']==prior,'wrong positivity chart')
    Z=var(fresh);r0=var(names['endpoint.r0']);F=var(names['fact0.output'])
    subs={names['y']:add(Z if prior else F,r0,const(1))}
    if prior:subs[names['M0']]=add(Z,const(-1))
    need({str(v):serial(p) for v,p in subs.items()}==certificate['substitutions'],'wrong endpoint substitution')
    # Bind the new abstract Z to the actual last square, not an asserted sign.
    if prior:
        cr=next(r for r in meta['rows'] if r['label']=='projected.carrier')
        def affine(a):
            if a not in defs:return var(a)
            p=restore(normrow(defs[a]),a)
            if any(len(m)>1 for m in p):return var(a)
            return substitute(p,{u:affine(u) for m in p for u in m})
        cp=substitute(normrow(cr),{u:affine(u) for m in normrow(cr) for u in m})
        candidates=[v for m,c in cp.items() if len(m)==1 and c==1 for v in m]
        need(len(candidates)==1,'carrier output ambiguous');zv=candidates[0]
        need(cp==add(var(zv),neg(var(names['M0'])),const(-1)),'carrier identity mismatch')
        zp=restore(normrow(defs[zv]),zv);need(len(zp)==1 and next(iter(zp.values()))==1,'carrier not square')
        mon=next(iter(zp));need(len(mon)==2 and mon[0]==mon[1],'carrier not exact square')
        need(certificate['abstract_Z']['index']==fresh,'abstract Z id')
    else:need(certificate['abstract_Z'] is None,'unexpected abstract Z')
    memo={}
    def expand(v):
        if v in subs:return subs[v]
        if v not in defs:return var(v)
        if v not in memo:
            rhs=restore(normrow(defs[v]),v)
            memo[v]=substitute(rhs,{u:expand(u) for m in rhs for u in m})
        return memo[v]
    er=next(r for r in meta['rows'] if r['label']=='endpoint.first_remainder')
    need(not substitute(normrow(er),{v:expand(v) for m in normrow(er) for v in m}),'endpoint substitution not justified')
    need(len(certificate['seeds'])==len(meta['seeds']),'seed count')
    leaves=set()
    for original,stored in zip(meta['seeds'],certificate['seeds']):
        need(original['exponent']==stored['exponent'] and original['pair']==stored['pair'],'seed identity')
        typ,v=original['exponent'];exp=const(v) if typ=='c' else expand(v)
        need(exp==collect(stored['positive_expansion']),'seed expansion mismatch')
        need(exp.get((),0)>=1 and all(c>=0 for c in exp.values()),'nonpositive seed')
        leaves|={v for m in exp for v in m}
    need(sorted(leaves)==certificate['nonnegative_leaf_indices'],'positive leaf list')
    for v in leaves:
        if prior and v==fresh:continue
        name=meta['variables'][v]['name'];need(name in retained and retained[name] in known,'unproved natural seed leaf')
    return {'seed_count':len(meta['seeds']),'endpoint_identity_checked':True,'carrier_square_checked':prior,'all_leaves_proved_natural':True}

def signed_domain(rawdir,sgndir):
    raw=read(rawdir/'equation.json');meta=read(rawdir/'raw_audit_input.json');mix=read(sgndir/'mixed_source.json');guarded=read(sgndir/'guarded.json');c=read(sgndir/'domain_certificate.json');budget=c['square_budget']
    names={v['name']:i for i,v in enumerate(raw['variables'])};gates={int(v):r for v,r in meta['gates'].items()};memo={}
    def atom(a):
        if a[0]=='c':return const(a[1])
        v=a[1];name=meta['variables'][v]['name']
        if name in names:return var(names[name])
        if v not in memo:
            r=meta['rows'][gates[v]];p=restore(normrow(r),v);imgs={w:atom(['v',w]) for m in p for w in m}
            memo[v]=substitute(p,imgs);need(all(len(m)<=1 for m in memo[v]),'nonaffine power port')
        return memo[v]
    ports=[];seen=set()
    for p in meta['powers']:
        for role in ['base','exponent','output']:
            a=p[role];key=tuple(a)
            if key not in seen:seen.add(key);ports.append({'token':a,'affine':serial(atom(a))})
    need(ports==budget['atoms'],'square budget port mismatch')
    expected_calls=[{role:serial(atom(p[role])) for role in ['base','exponent','output']} for p in meta['powers']]
    need(expected_calls==budget['power_calls'],'square budget calls mismatch')
    W=names['shared.W'];need(W==budget['frame_variable'],'wrong frame coordinate')
    rid=budget['frame_row']; rhs=add(const(2),*[mul(atom(a['token']),atom(a['token'])) for a in ports])
    new={'label':'shared.frame_definition','terms':serial(add(var(W),neg(rhs)))}
    need(raw['residuals'][rid]==budget['original_frame'] and budget['new_frame']==new,'frame change mismatch')
    expected=copy.deepcopy(raw);expected.pop('metrics',None);expected['residuals'][rid]=new
    need(expected==mix,'unexpected mixed source changes')
    known=set(c['guard_indices'])|{W};needed=set(c['semantic_required']);signed=set(c['semantic_signed'])
    for s in c['proof_steps']:
        v,rr,coef=s['variable'],s['row'],s['coefficient'];need(v not in known and coef>0,'invalid sign step')
        p=normrow(mix['residuals'][rr]);linear=p.get((v,));need(abs(linear)==coef,'wrong sign coefficient')
        rhs=collect(s['rhs']);expect=add({(v,):coef},neg(rhs))
        need(p==expect or neg(p)==expect,'sign identity')
        if s['kind']=='positive_monomials':
            need(all(cc>=0 for cc in rhs.values()),'negative sign monomial')
            deps={x for m in rhs for x,n in collections.Counter(m).items() if n%2}
            need(deps==set(s['dependencies']) and deps<=known,'unsigned dependency')
        elif s['kind']=='affine_square':
            root=collect(s['square_root']);need(all(len(m)<=1 for m in root),'nonaffine sign square');need(mul(root,root)==rhs,'false sign square')
            need(not s['dependencies'],'square has dependencies')
        else:raise ValueError('unknown sign rule')
        known.add(v)
    need(known==set(c['known_nonnegative']) and needed<=known,'sign closure incomplete')
    # Independent role policy: exemptions have exact names, not merely supplied IDs.
    import re
    patterns=[r'index[0-9]+\.(?:S|R|Squotient|Rquotient|X|Y)$',r'pow[0-9]+\.(?:quotient|output)$',r'shared_index\.(?:Bquotient|U)$',r'base[0-9]+\.T$',r'index_addition\.D$',r'range[0-9]+\.quotient$',r'choose[0-9]+\.high$',r'crt\.nonnegative_quotient$',r'endpoint\.(?:u0|ut)$',r'y$',r'M0$',r'crt\.index_quotient$']
    allowed={i for i,v in enumerate(mix['variables']) if any(re.fullmatch(p,v['name']) for p in patterns)}
    need(allowed==signed,'semantic exemption mismatch')
    need(needed=={i for i,v in enumerate(mix['variables']) if v['kind'] not in ['gate','square_difference']}-signed-{W},'required-role mismatch')
    expect=copy.deepcopy(mix);expect['domain']='unrestricted integers';expect['variant']+=':signed_square_budget'
    U=names['shared_index.U'];nz=c['nonzero_U_guard'];need(nz['variable']==U,'wrong U guard');seedproof=None
    if nz.get('omitted_by'):
        need(nz['omitted_by']=='presemantic_positive_seed_indices_v1' and nz['auxiliary']==[],'invalid U omission')
        seedproof=verify_positive_seeds(meta,c['presemantic_positive_seeds'],raw,known)
    else:
        a,b,d=range(len(expect['variables']),len(expect['variables'])+3)
        need([a,b,d]==nz['auxiliary'],'wrong U auxiliaries')
        expect['variables'] += [{'name':'nonzero_U.'+s,'kind':'integer_guard'} for s in ['a','b','c']]
        expect['residuals'].append({'label':'nonzero_U','terms':serial({(U,U):1,():-2,(a,a):-1,(b,b):-1,(d,d):-1,(d,):-1})})
    for v in c['guard_indices']:
        a,b,d=range(len(expect['variables']),len(expect['variables'])+3)
        expect['variables'] += [{'name':f'nonnegative.{v}.'+s,'kind':'integer_guard'} for s in ['a','b','c']]
        expect['residuals'].append({'label':f'nonnegative.{v}','terms':serial({(v,):1,(a,a):-1,(b,b):-1,(d,d):-1,(d,):-1})})
    need(expect==guarded,'unexpected guarded-source change')
    facts={}
    for name in ['t0','x','fact0.output','fact0.remainder','fact0.slack','choose0.output','choose0.oslack','choose1.output','shared.A','shared.Zminus1','shared_index.q4minus1','shared_index.Vquotient_minus1']:
        if name in names:facts[name]={'coordinate':names[name],'proved_nonnegative':names[name] in known}
    need(all(x['proved_nonnegative'] for x in facts.values()),'missing bootstrap sign')
    return {'guards':len(c['guard_indices']),'positive_sign_steps':len(c['proof_steps']),'power_ports':len(ports),'power_calls':len(expected_calls),'bootstrap_signs':facts,'presemantic_seed_positivity':seedproof,'verified':True}

def factorization(indir,outdir):
    src=read(indir/'guarded.json');tar=read(outdir/'factored_source.json');cert=read(outdir/'factorization_certificate.json')
    need(filehash(src)==cert['input_sha256'] and filehash(tar)==cert['output_sha256'],'factor hash')
    need(src['domain']=='unrestricted integers','signed factorization applied outside Z')
    rows=[normrow(r) for r in src['residuals']]; original=copy.deepcopy(rows);sq=cert['square_variables']; roots={int(v):collect(p) for v,p in cert['square_roots'].items()}
    need([src['variables'][s]['name'] for s in sq]==['sqd.'+str(i) for i in range(17)],'source square names')
    defs={s:row_for(src['residuals'],s,'nonnegative_square_difference') for s in sq}
    for s in sq:need(mul(roots[s],roots[s])==restore(rows[defs[s]],s),'false factor square root')
    chain=cert['product_chain'];need(len(chain)==11,'chain length');prev=sq[0]
    for (rid,out),f in zip(chain,sq[1:9]+['bundle',sq[13],sq[14]]):
        factor=add(var(sq[11]),var(sq[12])) if f=='bundle' else var(f)
        need(restore(rows[rid],out)==mul(var(prev),factor),'old product-chain identity');prev=out
    protected=set(sq[:9]+sq[13:15]+[v for _,v in chain[:-1]])
    allowed={defs[s] for s in sq[:9]+sq[13:15]}|{i for i,v in chain}
    need(all(not any(v in protected for m in p for v in m) for i,p in enumerate(rows) if i not in allowed),'ordinary factor escapes')
    expected=copy.deepcopy(src);expected.pop('metrics',None)
    for s in sq[:9]+sq[13:15]:rows[defs[s]]=add(var(s),neg(roots[s]));expected['variables'][s]['kind']='gate'
    (r9,o9),(r10,o10),(r11,o11)=chain[8:]
    rows[r9]=add(var(o9),neg(mul(var(chain[7][1]),var(sq[13]))));rows[r10]=add(var(o10),neg(mul(var(o9),var(sq[14]))));rows[r11]=add(var(o11),neg(mul(var(o10),var(o10))))
    root=len(expected['variables']);need(root==cert['new_root'],'new factor root');expected['variables'].append({'name':'factored.horn','kind':'gate'})
    for i,p in enumerate(rows):
        if i not in {rid for rid,v in chain}:rows[i]=substitute(p,{o11:var(root)})
    newrow=add(var(root),neg(mul(var(o11),add(var(sq[11]),var(sq[12])))))
    need(newrow==collect(cert['new_row']),'new Horn interface');rows.append(newrow);expected['residuals'].append({'label':'factored.horn'})
    gv=cert['guard_variables'];h,u,g,dv=gv['h'],gv['old_second_square'],gv['g'],gv['old_D_square']
    need((h,u)==tuple(sq[9:11]),'wrong guard roles')
    pr=row_for(src['residuals'],g);dr=row_for(src['residuals'],dv)
    need(restore(original[pr],g)==mul(var(h),var(u)),'old guard product')
    need(roots[sq[11]] in [add(var(g),neg(var(dv))),add(var(dv),neg(var(g)))],'old guard difference')
    D2=restore(original[dr],dv);need(all(len(m)<=2 for m in D2),'guard degree')
    guard_allowed={defs[h],defs[u],pr,dr,defs[sq[11]]}
    need(all(not any(v in {h,u,g,dv} for m in p for v in m) for i,p in enumerate(original) if i not in guard_allowed),'guard factor escapes')
    rows[defs[h]]=add(var(h),neg(mul(roots[h],roots[u])))
    rows[pr]=add(var(g),neg(mul(var(h),var(h))),D2)
    rows[defs[sq[11]]]=add(var(sq[11]),neg(mul(var(g),var(g))))
    deleted={defs[u],dr};need(deleted==set(cert['deleted_rows']),'deleted guard rows')
    expected['variables'][h]['kind']='gate'
    expected['residuals']=[{'label':expected['residuals'][i]['label'],'terms':serial(p)} for i,p in enumerate(rows) if i not in deleted]
    expected['variant']+=':signed_factorization';need(expected==tar,'unexpected factorized rows')
    return {'ordinary_squared_factors':11,'product_links':11,'guard_identity':'(L^2 M^2-D^2)^2=((LM)^2-D^2)^2','scope_escape_checks':True,'verified':True}

def integer_projection(outdir):
    src=read(outdir/'factored_source.json');tar=read(outdir/'equation.json');cert=read(outdir/'projection_certificate.json');need(filehash(src)==cert['input_sha256'] and filehash(tar)==cert['output_sha256'],'projection hashes')
    rows={i:normrow(r) for i,r in enumerate(src['residuals'])};live=set(range(len(src['variables'])))
    for s in cert['steps']:
        rid,v=s['row_id'],s['variable'];need(rid in rows and v in live,'dead integral pivot')
        rest=collect(s['restoration']);need(all(v not in m and set(m)<=live and len(m)<=2 and type(c)==int for m,c in rest.items()),'invalid integral restoration')
        expected=add(var(v),neg(rest));need(rows[rid]==expected or rows[rid]==neg(expected),'integral pivot identity')
        del rows[rid]
        for i,p in list(rows.items()):
            pp=substitute(p,{v:rest});need(all(len(m)<=2 for m in pp),'integral projection degree')
            if pp:rows[i]=pp
            else:del rows[i]
        live.remove(v)
    keep=cert['retained_original_variables'];unused=cert['unconstrained_removed']
    need(len(set(keep))==len(keep) and len(set(unused))==len(unused) and set(keep).isdisjoint(unused) and set(keep)|set(unused)==live,'integral coordinate partition')
    need({v for p in rows.values() for m in p for v in m}==set(keep),'integral used coordinates')
    need(sorted(rows)==cert['retained_original_rows'],'integral row partition');rename={v:i for i,v in enumerate(keep)}
    expected=[{'label':src['residuals'][i]['label'],'terms':serial(collect((c,tuple(rename[v] for v in m)) for m,c in p.items()))} for i,p in sorted(rows.items())]
    need(expected==tar['residuals'] and tar['variables']==[src['variables'][v] for v in keep],'integral target mismatch')
    pp=sos(tar);need(pp==collect(read(outdir/'expanded_polynomial.json')['terms']),'integer polynomial mismatch')
    return metrics(tar,pp)|{'eliminations':len(cert['steps']),'unconstrained_removed':len(unused),'verified':True}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('raw',type=Path);p.add_argument('signed',type=Path);p.add_argument('factored',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    res={'domain':signed_domain(a.raw,a.signed),'factorization':factorization(a.signed,a.factored),'projection':integer_projection(a.factored),'inputs':{}}
    for base in [a.raw,a.signed,a.factored]:
        for f in base.glob('*.json'):res['inputs'][str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
    a.output.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n');print(json.dumps({k:res[k] for k in ['domain','factorization','projection']},indent=2))
