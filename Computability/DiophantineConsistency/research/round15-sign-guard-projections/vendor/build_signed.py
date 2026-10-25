#!/usr/bin/env python3
"""Signed Pell compiler for the round14 hybrid, with auditable sign seeds.

The generic signed Pell lemma is inherited from the 553-integer release.
Unlike that release's old factorial, self-bounding fact0.output stays natural.
"""
from pathlib import Path
from collections import Counter,defaultdict,deque
import argparse,copy,hashlib,json,re
import terminal_elimination as E
from factor_horn import affine_root,add,neg,V

def inference(equation,exempt,axioms):
    rules=[]
    for rid,row in enumerate(equation['residuals']):
        p=E.normalize(row['terms'])
        for m,coef in p.items():
            if len(m)!=1:continue
            v=m[0];rhs={m:-c*(1 if coef>0 else -1) for m,c in p.items() if m!=(v,)}
            if any(v in m for m in rhs):continue
            root=None
            if all(c>=0 for c in rhs.values()):
                deps={k for m in rhs for k,e in Counter(m).items() if e%2};kind='positive_monomials'
            else:
                try:root=affine_root(rhs)
                except (ValueError,StopIteration):continue
                deps=set();kind='affine_square'
            rules.append((v,deps,rid,abs(coef),rhs,kind,root))
    rev=defaultdict(list)
    for i,(_,deps,*_) in enumerate(rules):
        for d in deps:rev[d].append(i)
    def closure(seed):
        known=set(seed)|set(axioms);pending=[len(ds-known) for _,ds,*_ in rules]
        q=deque(i for i,n in enumerate(pending) if n==0);proof=[]
        while q:
            i=q.popleft();v,deps,rid,c,rhs,kind,root=rules[i]
            if v in known:continue
            known.add(v);step={'variable':v,'row':rid,'coefficient':c,'dependencies':sorted(deps),'rhs':E.as_terms(rhs),'kind':kind}
            if root is not None:step['square_root']=E.as_terms(root)
            proof.append(step)
            for j in rev[v]:
                pending[j]-=1
                if pending[j]==0:q.append(j)
        return known,proof
    required={i for i,v in enumerate(equation['variables']) if v['kind'] not in ('gate','square_difference')}-exempt-set(axioms)
    seed=set(required)
    for i in sorted(seed,reverse=True):
        if required<=closure(seed-{i})[0]:seed.remove(i)
    known,proof=closure(seed)
    if not required<=known:raise ValueError('incomplete sign closure')
    return {'guard_indices':sorted(seed),'proof_steps':proof,'known_nonnegative':sorted(known),'semantic_required':sorted(required),'semantic_signed':sorted(exempt),'undetermined':sorted(set(range(len(equation['variables'])))-known)}

def square_budget(equation,raw):
    retained={v['name']:i for i,v in enumerate(equation['variables'])}
    bygate={r['gate']:r for r in raw['rows'] if 'gate' in r};memo={};steps=[]
    def atom(a):
        if a[0]=='c':return {():a[1]} if a[1] else {}
        v=a[1];name=raw['variables'][v]['name']
        if name in retained:return V(retained[name])
        if v in memo:return memo[v]
        p=E.normalize(bygate[v]['terms']);rest=E.candidate(p,v,False)
        if rest is None:raise ValueError('not monic')
        result={}
        for m,c in rest.items():
            value={():c}
            for w in m:value=E.multiply(value,atom(['v',w]))
            result=add(result,value)
        if E.degree(result)>1:raise ValueError('nonaffine port')
        memo[v]=result;steps.append({'raw_variable':v,'name':name,'restoration':E.as_terms(result)})
        return result
    atoms=[];seen=set()
    for power in raw['powers']:
        for role in ('base','exponent','output'):
            a=power[role];key=tuple(a)
            if key not in seen:seen.add(key);atoms.append({'token':a,'affine':E.as_terms(atom(a))})
    W=retained['shared.W'];rhs={():2}
    for a in atoms:
        p=E.normalize(a['affine']);rhs=add(rhs,E.multiply(p,p))
    e=copy.deepcopy(equation);e.pop('metrics',None)
    rows=[i for i,r in enumerate(e['residuals']) if r['label']=='shared.frame_definition']
    if len(rows)!=1:raise ValueError('frame definition')
    rid=rows[0];old=e['residuals'][rid];new=dict(old,terms=E.as_terms(add(V(W),neg(rhs))))
    e['residuals'][rid]=new
    cert={'frame_variable':W,'frame_row':rid,'atoms':atoms,'atom_expansions':steps,'original_frame':old,'new_frame':new,
          'power_calls':[{k:E.as_terms(atom(p[k])) for k in ('base','exponent','output')} for p in raw['powers']]}
    return e,cert

def positive_seed_certificate(raw):
    """Prove every seed exponent positive before using any power graph.

    Expand only defining gates. At semantic leaves substitute the proved
    endpoint identities; Z denotes M0+1, a square in the old carrier chart.
    """
    names={v['name']:i for i,v in enumerate(raw['variables'])}
    defs={r['gate']:r for r in raw['rows'] if r.get('gate') is not None}
    prior='M0' in names
    fresh=len(raw['variables']);z=V(fresh);r0=V(names['endpoint.r0'])
    F=V(names['fact0.output'])
    subst={names['y']:add(z if prior else F,r0,{():1})}
    if prior:subst[names['M0']]=add(z,{():-1})
    # A derived-label binomial may request an enormous constructor polynomial
    # as an index. Certify positivity compositionally, without expanding it.
    leaf_bounds={i:0 for n,i in names.items() if n in ('t0','x','fact0.output','endpoint.r0') or n.startswith('crt.encoded.') or n=='crt.encoded_index_minus_one'}
    leaf_bounds[names['y']]=1
    if prior:leaf_bounds[names['M0']]=-1
    bounds={};bound_steps=[]
    def lower(a):
        if a[0]=='c':return a[1]
        v=a[1]
        if v in leaf_bounds:return leaf_bounds[v]
        if v in bounds:return bounds[v]
        if v not in defs:raise ValueError(('unproved seed leaf',v,raw['variables'][v]['name']))
        rhs=E.candidate(E.normalize(defs[v]['terms']),v,False)
        if rhs is None or any(c<0 for c in rhs.values()):raise ValueError('not a monotone seed gate')
        val=0;dependencies={}
        for m,c in rhs.items():
            a=c
            for u in m:
                b=lower(['v',u]);dependencies[u]=b
                if len(m)>1 and b<0:raise ValueError('nonlinear negative seed bound')
                a*=b
            val+=a
        result=min(64,val)
        bounds[v]=result;bound_steps.append({'variable':v,'row':defs[v],'dependencies':[[i,b] for i,b in sorted(dependencies.items())],'lower_bound':result})
        return result
    seed_bounds=[]
    for s in raw['seeds']:
        bound=lower(s['exponent'])
        if bound<1:raise ValueError('nonpositive compositional seed')
        seed_bounds.append({'exponent':s['exponent'],'pair':s['pair'],'lower_bound':bound})
    if any(raw['variables'][s['exponent'][1]]['name'].startswith('derived') for s in raw['seeds']) or raw.get('derived_label_range') or len(bound_steps)>200:
        return {'schema':'presemantic_positive_seed_indices_v2','prior_carrier':prior,'seeds':seed_bounds,'proof_steps':bound_steps,'leaf_bounds':[[i,b] for i,b in sorted(leaf_bounds.items())],
                'conclusion':'All seed exponents are positive before power recovery; their guarded Y>=k give V>0 and |U|>=2.'}
    memo={};steps=[]
    def atom(a):
        if a[0]=='c':return {():a[1]} if a[1] else {}
        v=a[1]
        if v in subst:return subst[v]
        if v not in defs:return V(v)
        if v in memo:return memo[v]
        rhs=E.candidate(E.normalize(defs[v]['terms']),v,False)
        if rhs is None:raise ValueError('seed definition is not monic')
        value={}
        for m,c in rhs.items():
            p={():c}
            for u in m:p=E.multiply(p,atom(['v',u]))
            value=add(value,p)
        memo[v]=value;steps.append({'variable':v,'row':defs[v],'expanded':E.as_terms(value)})
        return value
    seeds=[]
    for s in raw['seeds']:
        p=atom(s['exponent'])
        if not all(c>=0 for c in p.values()) or p.get((),0)<1:raise ValueError('nonpositive seed certificate')
        seeds.append({'exponent':s['exponent'],'pair':s['pair'],'positive_expansion':E.as_terms(p)})
    leaves=sorted({i for s in seeds for c,m in s['positive_expansion'] for i in m})
    allowed={names[n] for n in names if n in ('t0','x','fact0.output','endpoint.r0') or n.startswith('crt.encoded.') or n=='crt.encoded_index_minus_one'}|({fresh} if prior else set())
    if not set(leaves)<=allowed:raise ValueError(('unproved seed leaves',set(leaves)-allowed))
    return {'schema':'presemantic_positive_seed_indices_v1','prior_carrier':prior,'substitutions':{str(i):E.as_terms(p) for i,p in subst.items()},
        'abstract_Z':{'index':fresh,'meaning':'M0+1 is the last squared carrier gate'} if prior else None,
        'seeds':seeds,'expansion_steps':steps,'nonnegative_leaf_indices':leaves,
        'conclusion':'Every seed Y=k+e is positive. V=product(Y^2)*(v+1)>0. The auxiliary norm therefore forces U^2>=A^2>=4 without a new guard.'}

def build(rawdir,out,cap=16,drop_u=False):
    raw=json.loads((rawdir/'raw_audit_input.json').read_text());original=json.loads((rawdir/'equation.json').read_text())
    source,budget=square_budget(original,raw)
    pats=[r'index[0-9]+\.(?:S|R|Squotient|Rquotient|X|Y)$',r'pow[0-9]+\.(?:quotient|output)$',r'shared_index\.(?:Bquotient|U)$',r'base[0-9]+\.T$',r'index_addition\.D$',r'range[0-9]+\.quotient$',r'choose[0-9]+\.high$',r'crt\.nonnegative_quotient$',r'endpoint\.(?:u0|ut)$',r'y$',r'M0$',r'crt\.index_quotient$']
    exempt={i for i,v in enumerate(source['variables']) if any(re.fullmatch(p,v['name']) for p in pats)}
    proof=inference(source,exempt,[budget['frame_variable']]);proof['square_budget']=budget
    e=copy.deepcopy(source);e['domain']='unrestricted integers';e['variant']+=':signed_square_budget'
    U=next(i for i,v in enumerate(e['variables']) if v['name']=='shared_index.U')
    if drop_u:
        proof['presemantic_positive_seeds']=positive_seed_certificate(raw)
        proof['nonzero_U_guard']={'variable':U,'auxiliary':[],'omitted_by':'presemantic_positive_seed_indices_v1'}
    else:
        a,b,c=range(len(e['variables']),len(e['variables'])+3)
        e['variables'] += [{'name':'nonzero_U.'+s,'kind':'integer_guard'} for s in ('a','b','c')]
        e['residuals'].append({'label':'nonzero_U','terms':E.as_terms({(U,U):1,():-2,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
        proof['nonzero_U_guard']={'variable':U,'auxiliary':[a,b,c]}
    for v in proof['guard_indices']:
        a,b,c=range(len(e['variables']),len(e['variables'])+3)
        e['variables'] += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        e['residuals'].append({'label':f'nonnegative.{v}','terms':E.as_terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    target,cert,metrics=E.optimize(e,max_support=cap);receipt=E.verify(e,target,cert)
    out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('mixed_source.json',source),('guarded.json',e),('domain_certificate.json',proof),('equation.json',target),('projection_certificate.json',cert),('expanded_polynomial.json',E.expand(target)),('METRICS.json',metrics|receipt|{'guards':len(proof['guard_indices'])})]:
        (out/name).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(metrics|receipt|{'guards':len(proof['guard_indices'])},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('raw',type=Path);p.add_argument('output',type=Path);p.add_argument('--cap',type=int,default=16);p.add_argument('--drop-u-guard',action='store_true');a=p.parse_args();build(a.raw,a.output,a.cap,a.drop_u_guard)
