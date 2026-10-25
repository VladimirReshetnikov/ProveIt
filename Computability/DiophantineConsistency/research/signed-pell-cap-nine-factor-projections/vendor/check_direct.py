#!/usr/bin/env python3
"""Independent, assertion-free replay of round15 literal certificates.

Imports only Python standard-library modules. No producer, eliminator, or
arithmetic compiler is imported. Algebraic checks supplement the written
unbounded proof; they cannot establish consistency or decide solvability.
"""
import argparse, copy, hashlib, json, re
from collections import defaultdict, Counter
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def need(b,s):
    if not b: raise ValueError(s)
def canon(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(x): return hashlib.sha256(canon(x)).hexdigest()
def get(p): return json.loads(p.read_text())
def norm(terms):
    if isinstance(terms,dict) and 'terms' in terms: terms=terms['terms']
    d=defaultdict(int)
    for c,m in terms:
        need(type(c) is int,'noninteger coefficient')
        need(all(type(i) is int and i>=0 for i in m),'invalid monomial')
        d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}
def terms(p): return [[c,list(m)] for m,c in sorted(p.items())]
def add(*ps):
    d=defaultdict(int)
    for p in ps:
        for m,c in p.items(): d[m]+=c
    return {m:c for m,c in d.items() if c}
def sc(p,a): return {m:a*c for m,c in p.items() if a*c}
def mul(p,q):
    d=defaultdict(int)
    for m,c in p.items():
        for n,b in q.items(): d[tuple(sorted(m+n))]+=c*b
    return {m:c for m,c in d.items() if c}
def v(i): return {(i,):1}
def con(n): return {():n} if n else {}
def sub(p,i,r):
    d={}
    for m,c in p.items():
        a=con(c)
        for j in m: a=mul(a,r if j==i else v(j))
        d=add(d,a)
    return d
def deg(p): return max(map(len,p),default=0)
def solved(p,i):
    a=p.get((i,),0)
    need(a in (1,-1),'nonmonic definition')
    rest={m:c for m,c in p.items() if m!=(i,)}
    need(not any(i in m for m in rest),'self definition')
    return sc(rest,-a)
def equivalent(p,q): return p==q or p==sc(q,-1)

def literal(eq):
    n=len(eq['variables']);used=set();out={}
    need(len({x['name'] for x in eq['variables']})==n,'duplicate names')
    for r in eq['residuals']:
        p=norm(r);need(deg(p)<=2,'nonquadratic row')
        used.update(i for m in p for i in m)
        need(all(i<n for m in p for i in m),'coordinate beyond census')
        out=add(out,mul(p,p))
    return out,used

def projection(src,dst,cert,natural=False):
    if natural:
        hk=('source_equation_sha256','target_equation_sha256')
        live=cert['retained_original_indices_in_target_order'];keep=cert['surviving_source_row_ids_in_target_order']
        unused=cert['unused_original_indices_restored_to_zero']
    else:
        hk=('input_sha256','output_sha256');live=cert['retained_original_variables'];keep=cert['retained_original_rows'];unused=cert['unconstrained_removed']
    hasher=(lambda x:hashlib.sha256(canon(x).rstrip(b'\n')).hexdigest()) if natural else sha
    need(hasher(src)==cert[hk[0]] and hasher(dst)==cert[hk[1]],'projection hash binding')
    rows={i:norm(r) for i,r in enumerate(src['residuals'])};deleted=set();zeros=set()
    for s in cert['steps']:
        i=s['variable_original_index'] if natural else s['variable'];rid=s['source_row_id'] if natural else s['row_id'];f=norm(s['restoration'])
        need(i not in deleted and rid in rows,'projection target missing')
        need(deg(f)<=2 and not any(i in m for m in f),'projection restoration invalid')
        need(not any(j in deleted for m in f for j in m),'projection stale dependency')
        need(equivalent(rows[rid],add(v(i),sc(f,-1))),'projection equation mismatch')
        if natural:
            nc=s['nonnegative_certificate'];rem=norm(nc['nonnegative_remainder'])
            need(all(c>=0 for c in rem.values()),'negative certificate remainder')
            represented=dict(rem)
            for square in nc['squares']:
                weight=Fraction(*square['weight']);need(weight>=0,'negative square weight')
                form={tuple(m):Fraction(*c) for c,m in square['affine_form']};need(deg(form)<=1,'nonaffine square')
                represented=add(represented,sc(mul(form,form),weight))
            need(represented==f,'invalid natural nonnegative certificate')
        del rows[rid]
        for j in list(rows):
            rows[j]=sub(rows[j],i,f);need(deg(rows[j])<=2,'projection degree increased')
            if not rows[j]:zeros.add(j);del rows[j]
        deleted.add(i)
    need(keep==sorted(rows),'surviving row map')
    need(live==sorted({i for p in rows.values() for m in p for i in m}),'surviving coordinate map')
    need(unused==sorted(set(range(len(src['variables'])))-set(live)-deleted),'unused map')
    remap={x:i for i,x in enumerate(live)}
    expected=[{'label':src['residuals'][j]['label'],'terms':terms({tuple(remap[i] for i in m):c for m,c in rows[j].items()})} for j in keep]
    need(dst['residuals']==expected,'projection literal rows')
    need(dst['variables']==[src['variables'][i] for i in live],'projection literal coordinates')
    return len(cert['steps'])

def square_budget(raw,original,b):
    retained={x['name']:i for i,x in enumerate(original['variables'])};defs={r['gate']:norm(r) for r in raw['rows'] if r.get('gate') is not None};cache={};busy=set()
    def atom(t):
        if t[0]=='c':return con(t[1])
        i=t[1];name=raw['variables'][i]['name']
        if name in retained:return v(retained[name])
        if i in cache:return cache[i]
        need(i not in busy and i in defs,'raw atom definition unavailable');busy.add(i)
        d={}
        for m,c in solved(defs[i],i).items():
            z=con(c)
            for j in m:z=mul(z,atom(['v',j]))
            d=add(d,z)
        busy.remove(i);need(deg(d)<=1,'power atom not affine');cache[i]=d;return d
    expected=[];seen=set()
    for p in raw['powers']:
        for role in ('base','exponent','output'):
            token=tuple(p[role])
            if token not in seen:seen.add(token);expected.append({'token':list(token),'affine':terms(atom(token))})
    need(expected==b['atoms'],'incomplete frame atom set')
    calls=[{k:terms(atom(p[k])) for k in ('base','exponent','output')} for p in raw['powers']]
    need(calls==b['power_calls'],'power-call port mismatch')
    W=b['frame_variable'];need(original['variables'][W]['name']=='shared.W','wrong frame coordinate')
    rid=b['frame_row'];need(original['residuals'][rid]==b['original_frame'],'wrong original frame')
    rhs=con(2)
    for a in expected:rhs=add(rhs,mul(norm(a['affine']),norm(a['affine'])))
    need(norm(b['new_frame'])==add(v(W),sc(rhs,-1)),'square frame mismatch')
    return calls,atom

def source_transform(raw,original,source,c):
    need(original['domain']=='nonnegative integers' and source['domain']=='unrestricted integers','source domain mismatch')
    need(c['raw_sha256']==sha(raw) and c['original_sha256']==sha(original) and c['source_sha256']==sha(source),'transformation hash binding')
    calls,atom=square_budget(raw,original,c['square_budget']);rows=copy.deepcopy(original['residuals']);b=c['square_budget'];rows[b['frame_row']]=b['new_frame']
    names={x['name']:i for i,x in enumerate(source['variables'])}
    t=raw['powers'][0]['exponent'];K=raw['powers'][1]['exponent']
    need(c['undoubled_seed_exponents']==[t,K],'undoubled indices differ')
    wantseeds=[s for s in raw['seeds'] if s['exponent'] not in [t,K]]
    need([s['exponent'] for s in c['seeds']]==[s['exponent'] for s in wantseeds],'selective seed set')
    selected=sorted(i for i,p in enumerate(raw['powers']) if any(p['exponent']==s['exponent'] for s in wantseeds))
    need(selected==c['selected_calls'],'selected power set')
    allowed={}
    for s,want in zip(c['seeds'],wantseeds):
        pair=[names[raw['variables'][a[1]]['name']] for a in want['pair']]
        need(s['pair']==pair,'seed pair mismatch')
        need(s['prefix']==source['variables'][pair[0]]['name'].split('.')[0],'seed prefix')
        ids=[i for i,p in enumerate(raw['powers']) if p['exponent']==want['exponent']]
        need(ids==s['calls'],'seed call group')
        exponent=norm(calls[ids[0]]['exponent']);need(exponent==norm(s['affine_exponent']),'seed exponent mismatch')
        label=s['prefix']+'.R_mod_4Y';rids=[i for i,r in enumerate(rows) if r['label']==label];need(len(rids)==1,'seed residue missing')
        rid=rids[0];allowed[rid]=('double_seed_index',add(norm(rows[rid]),sc(exponent,-1)))
    for i in selected:
        rids=[j for j,r in enumerate(rows) if r['label']==f'pow{i}.power_congruence'];need(len(rids)==1,'power row missing');rid=rids[0]
        m=norm(calls[i]['output']);allowed[rid]=('square_output',add(norm(rows[rid]),m,sc(mul(m,m),-1)))
    rid=b['frame_row'];allowed[rid]=('double_square_frame',add(sc(norm(rows[rid]),2),sc(v(b['frame_variable']),-1)))
    need(len(c['changes'])==len(allowed),'unexpected transform changes')
    for ch in c['changes']:
        rid=ch['row'];need(rid in allowed,'unrequested changed row');kind,p=allowed.pop(rid)
        need(ch['kind']==kind and rows[rid]==ch['old'] and norm(ch['new'])==p,'incorrect transform rewrite');rows[rid]=ch['new']
    need(not allowed,'missing transform rewrite')
    q=atom(raw['radix']['radix']);qplus=add(q,con(1));orient=c['orientation'];need([x['call'] for x in orient]==selected,'power orientations incomplete')
    additions=[]
    for item in orient:
        call=calls[item['call']];base=norm(call['base']);m=norm(call['output'])
        need(item['output']==call['output'],'orientation output')
        if item['kind']=='residue_one':
            need(base==qplus and norm(item['radix'])==q,'residue-one base mismatch')
            u=item['quotient'];need(u>=len(original['variables']),'residue witness not fresh')
            expected={'label':f'residue_one.pow{item["call"]}','terms':terms(add(m,con(-1),sc(mul(q,v(u)),-1)))}
            need(item['row']==len(rows)+len(additions),'residue row order');additions.append(expected)
        elif item['kind']=='residue_reparameterization':
            need(base==qplus and norm(item['radix'])==q,'reparameterized base mismatch')
            u=item['quotient'];replacement=add(con(1),mul(q,v(u)))
            need(norm(item['old_remainder'])==replacement,'remainder substitution formula')
            need(source['variables'][u]['name'].endswith('.remainder'),'reparameterized wrong coordinate')
            occurrences=[j for j,r in enumerate(rows) if any(u in mon for mon in norm(r))]
            need([ch['row'] for ch in item['changes']]==occurrences,'incomplete remainder substitution')
            for ch in item['changes']:
                j=ch['row'];need(rows[j]==ch['old'],'remainder old row mismatch')
                new=sub(norm(rows[j]),u,replacement);need(deg(new)<=2 and norm(ch['new'])==new,'remainder substituted row mismatch');rows[j]=ch['new']
            need(item['digit_row'] in occurrences,'missing terminal digit relation')
        else:need(item['kind']=='nonnegative_remainder_bound' and base==q,'unsupported output orientation')
    need(source['residuals']==rows+additions,'complete transformed source differs')
    need(source['variables'][:len(original['variables'])]==original['variables'],'source variables changed')
    interval=copy.deepcopy(original);interval.pop('metrics',None);interval['domain']='unrestricted integers';interval['variant']+=':residue_even_v1';interval['residuals'][b['frame_row']]=b['new_frame']
    need(c.get('interval_reference_sha256')==sha(interval),'interval reference binding')
    need(len(source['variables'])==len(original['variables'])+len(additions),'source extra variables')
    return calls

def domain(source,guarded,c):
    reparams={x['quotient']:norm(x['old_remainder']) for x in c['orientation'] if x['kind']=='residue_reparameterization'}
    p=c['sign_inference'];W=c['square_budget']['frame_variable'];names={x['name']:i for i,x in enumerate(source['variables'])};commonV=names['shared_index.V']
    pats=[r'index[0-9]+\.(?:S|R|Squotient|Rquotient|X|Y)$',r'pow[0-9]+\.(?:quotient|output)$',r'shared_index\.(?:Bquotient|U|Vquotient_minus1)$',r'base[0-9]+\.T$',r'index_addition\.D$',r'range[0-9]+\.quotient$',r'choose[0-9]+\.high$',r'crt\.nonnegative_quotient$',r'endpoint\.(?:u0|ut)$',r'y$',r'M0$',r'crt\.index_quotient$',r'residue_one\..*']
    exempt={i for i,x in enumerate(source['variables']) if any(re.fullmatch(pattern,x['name']) for pattern in pats)}|{names[s['prefix']+'.YminusK'] for s in c['seeds']}
    required={i for i,x in enumerate(source['variables']) if x['kind'] not in ('gate','square_difference')}-exempt-{W,commonV}
    need(exempt==set(p['semantic_signed']) and required==set(p['semantic_required']),'semantic sign interface mismatch')
    originalguards=set(p['guard_indices']);actual=set(g['coordinate'] for g in c['guards'] if g['kind']=='nonnegative')
    need(len(actual)==sum(g['kind']=='nonnegative' for g in c['guards']),'duplicate scalar guard')
    pairs=set()
    for pair in c['paired_guards']:
        a,b=pair['pair'];x,y=pair['anchor'];need({a,b,x,y}<=originalguards,'pair premise not originally guarded');need({x,y}<=actual,'unguarded pair anchor')
        upper=norm(pair['upper']);need(deg(upper)<=1 and all(a>=0 for a in upper.values()),'bad pair upper')
        for rid,r,s in [(pair['row'],a,b),(pair['anchor_row'],x,y)]:
            expected=add(upper,sc(v(r),-1),sc(v(s),-1),con(-1))
            for u,replacement in reparams.items():expected=sub(expected,u,replacement)
            need(norm(source['residuals'][rid])==expected,'pair weighted-sum identity')
        need((a in reparams)==(x in reparams) and b not in reparams and y not in reparams,'incompatible weighted anchors')
        need(not pairs.intersection([a,b]),'pair reuse');pairs.update([a,b])
    need(actual|pairs==originalguards and not actual&pairs,'guard replacement coverage')
    gs=copy.deepcopy(source);n=len(gs['variables']);pos=0;pairset=set()
    for j,g in enumerate(c['guards']):
        if g['kind']=='nonnegative':expr=v(g['coordinate'])
        elif g['kind']=='positive_common_V':expr=add(v(commonV),con(-1));pos+=1
        else:
            need(g['kind']=='paired_interval','unknown guard');a,b=g['pair'];expr=mul(v(a),v(b));pairset.add(tuple(g['pair']))
        need(norm(g['expression'])==expr,'guard expression mismatch')
        aux=list(range(n,n+3));need(g['auxiliary']==aux,'nonfresh guard witnesses');n+=3
        gs['variables'] += [{'name':f'guard{j}.{s}','kind':'integer_guard'} for s in ['a','b','c']]
        a,b,d=aux;expected={'label':f'domain_guard.{j}','terms':terms(add(expr,{(a,a):-1,(b,b):-1,(d,d):-1,(d,):-1}))}
        need(g['row']==len(gs['residuals']),'guard row number');gs['residuals'].append(expected)
    need(pos==1 and pairset=={tuple(p['pair']) for p in c['paired_guards']},'guard inventory')
    need(gs==guarded,'complete guarded equation differs')
    known=originalguards|{W,commonV}
    for step in p['proof_steps']:
        i=step['variable'];row=norm(source['residuals'][step['row']]);coef=step['coefficient'];rhs=norm(step['rhs'])
        need(coef>0 and equivalent(row,add(sc(v(i),coef),sc(rhs,-1))),'sign inference row identity')
        if step['kind']=='positive_monomials':
            need(all(c>=0 for c in rhs.values()),'negative monomial sign proof');deps={j for m in rhs for j,e in Counter(m).items() if e%2}
            need(deps==set(step['dependencies']) and deps<=known,'sign proof missing premise')
        else:
            need(step['kind']=='affine_square' and not step['dependencies'],'unknown sign proof');r=norm(step['square_root']);need(deg(r)<=1 and mul(r,r)==rhs,'invalid sign square')
        known.add(i)
    need(known==set(p['known_nonnegative']),'sign closure census')
    need(set(p['semantic_required'])<=known,'unproved semantic sign')
    for name in ['t0','x','fact0.output','fact0.remainder','fact0.slack','endpoint.r0','shared.A','shared.Zminus1','index0.YminusK','index1.YminusK']:
        need(names[name] in known,'missing bootstrap sign '+name)
    return len(c['guards'])

def seed_positivity(raw,source,cert):
    need(cert['prior_carrier'] is False,'unexpected carrier in seed proof')
    raw_names={x['name']:i for i,x in enumerate(raw['variables'])};names={x['name']:i for i,x in enumerate(source['variables'])}
    leaves={i:0 for name,i in raw_names.items() if name in ('t0','x','fact0.output','endpoint.r0') or name.startswith('crt.encoded.') or name=='crt.encoded_index_minus_one'}
    leaves[raw_names['y']]=1
    need(dict(cert['leaf_bounds'])==leaves,'seed leaf bounds')
    endpoint=[norm(r) for r in source['residuals'] if r['label']=='endpoint.first_remainder']
    need(len(endpoint)==1 and equivalent(endpoint[0],add(v(names['y']),sc(v(names['fact0.output']),-1),sc(v(names['endpoint.r0']),-1),con(-1))),'seed y positivity identity')
    defs={r['gate']:r for r in raw['rows'] if r.get('gate') is not None};lower=dict(leaves)
    for step in cert['proof_steps']:
        i=step['variable'];need(i in defs and defs[i]==step['row'],'seed gate source binding')
        rhs=solved(norm(step['row']),i);need(all(c>=0 for c in rhs.values()),'nonmonotone seed constructor')
        deps={j:lower[j] for m in rhs for j in m}
        need(step['dependencies']==[[j,x] for j,x in sorted(deps.items())],'seed lower dependency')
        value=0
        for m,c in rhs.items():
            term=c
            for j in m:term*=lower[j]
            value+=term
        bound=min(64,value);need(bound==step['lower_bound'],'seed lower evaluation');lower[i]=bound
    need(len(cert['seeds'])==len(raw['seeds']),'seed positivity census')
    bounds=[]
    for s,r in zip(cert['seeds'],raw['seeds']):
        need(s['exponent']==r['exponent'] and s['pair']==r['pair'],'seed positivity binding')
        t=s['exponent'];b=t[1] if t[0]=='c' else lower[t[1]]
        need(b==s['lower_bound'] and b>=1,'nonpositive seed index');bounds.append(b)
    return bounds

def pruning(src,dst,c,seeds):
    need(sha(src)==c['input_sha256'] and sha(dst)==c['output_sha256'],'pruning hash binding')
    names={x['name']:i for i,x in enumerate(src['variables'])}
    need([r['variable'] for r in c['dropped_private_slacks']]==[names[s['prefix']+'.YminusK'] for s in seeds],'pruned slack set')
    dropped=set()
    for s in c['dropped_private_slacks']:
        i,r=s['variable'],s['row'];hits=[j for j,row in enumerate(src['residuals']) if any(i in m for m in norm(row))]
        need(hits==[r],'pruned slack not private')
        need(solved(norm(src['residuals'][r]),i)==norm(s['restoration']),'pruned slack restoration')
        dropped.add(r)
    e=copy.deepcopy(src);e['residuals']=[r for j,r in enumerate(src['residuals']) if j not in dropped]
    need(e==dst,'pruning literal replay')
    return len(dropped)

def factorization(src,dst,c):
    need(sha(src)==c['input_sha256'] and sha(dst)==c['output_sha256'],'factorization hash')
    rows=[norm(r) for r in src['residuals']];sq=c['square_variables'];need([src['variables'][i]['name'] for i in sq]==['sqd.'+str(i) for i in range(17)],'factor square interface')
    defs={}
    roots={int(i):norm(r) for i,r in c['square_roots'].items()}
    for s in sq:
        hits=[j for j,p in enumerate(rows) if p.get((s,))==1 and src['residuals'][j]['label']=='nonnegative_square_difference'];need(len(hits)==1,'square defining row census');defs[s]=hits[0]
        need(deg(roots[s])<=1 and solved(rows[hits[0]],s)==mul(roots[s],roots[s]),'factor square root mismatch')
    chain=[tuple(x) for x in c['product_chain']];factors=sq[:9]+['bundle',sq[13],sq[14]];previous=factors[0]
    for (rid,out),f in zip(chain,factors[1:]):
        right=add(v(sq[11]),v(sq[12])) if f=='bundle' else v(f)
        need(solved(rows[rid],out)==mul(v(previous),right),'Horn chain identity');previous=out
    need(len(chain)==11,'Horn chain length');protected=set(sq[:9]+sq[13:15]+[x for _,x in chain[:-1]])
    allowed={defs[s] for s in sq[:9]+sq[13:15]}|{i for i,_ in chain}
    need(not any(rid not in allowed and any(i in protected for m in row for i in m) for rid,row in enumerate(rows)),'signed factor escapes')
    # Replay exact edits, then check the complete polynomial boundary by substituting
    # only this small internal circuit. Named external atoms remain indeterminates.
    oldrows=copy.deepcopy(rows)
    for ch in c['changes']:
        rid=ch['row'];need(rows[rid]==norm(ch['old']),'factor edit old row');rows[rid]=norm(ch['new'])
    root=c['new_root'];need(root==len(src['variables']),'new root not fresh');rows.append(norm(c['new_row']))
    deleted=set(c['deleted_rows']);e=copy.deepcopy(src);e.pop('metrics',None);e['variant']+=':signed_factorization'
    for s in sq[:9]+sq[13:15]+[c['guard_variables']['h']]:e['variables'][s]['kind']='gate'
    e['variables'].append({'name':'factored.horn','kind':'gate'});base=src['residuals']+[{'label':'factored.horn'}]
    e['residuals']=[{'label':base[j]['label'],'terms':terms(p)} for j,p in enumerate(rows) if j not in deleted]
    need(e==dst,'factorization literal replay')
    # The only permitted rules are the eleven affine roots, three reordered
    # products, one external old-root substitution, and three guard identities.
    expected={}
    for s in sq[:9]+sq[13:15]:expected[defs[s]]=add(v(s),sc(roots[s],-1))
    (r9,o9),(r10,o10),(r11,o11)=chain[8:]
    expected.update({r9:add(v(o9),sc(mul(v(chain[7][1]),v(sq[13])),-1)),r10:add(v(o10),sc(mul(v(o9),v(sq[14])),-1)),r11:add(v(o11),sc(mul(v(o10),v(o10)),-1))})
    need(norm(c['new_row'])==add(v(root),sc(mul(v(o11),add(v(sq[11]),v(sq[12]))),-1)),'factored Horn final product')
    for j,p in enumerate(oldrows):
        if j not in {rid for rid,_ in chain} and any(o11 in m for m in p):expected[j]=sub(p,o11,v(root))
    g=c['guard_variables'];h,u,z,d=(g[k] for k in ('h','old_second_square','g','old_D_square'))
    need(h==sq[9] and u==sq[10],'guard variables')
    pr=[j for j,p in enumerate(oldrows) if p.get((z,)) in (-1,1) and not any(z in m for m in p if m!=(z,)) and solved(p,z)==mul(v(h),v(u))];need(len(pr)==1,'guard old product')
    dr=[j for j,p in enumerate(oldrows) if p.get((d,)) in (-1,1) and not any(d in m for m in p if m!=(d,))];need(len(dr)==1,'guard square definition')
    D2=solved(oldrows[dr[0]],d);guardroot=roots[sq[11]];need(guardroot in [add(v(z),sc(v(d),-1)),add(v(d),sc(v(z),-1))],'guard boundary difference')
    expected.update({defs[h]:add(v(h),sc(mul(roots[h],roots[u]),-1)),pr[0]:add(v(z),sc(mul(v(h),v(h)),-1),D2),defs[sq[11]]:add(v(sq[11]),sc(mul(v(z),v(z)),-1))})
    need(deleted=={defs[u],dr[0]},'wrong deleted guard definitions')
    guardallowed={defs[h],defs[u],pr[0],dr[0],defs[sq[11]]}
    need(not any(j not in guardallowed and any(i in {h,u,z,d} for m in p for i in m) for j,p in enumerate(oldrows)),'guard variables escape')
    need({ch['row']:norm(ch['new']) for ch in c['changes']}==expected,'unproved factorization edit')
    return len(c['changes'])

def translation(src,dst,c):
    need(sha(src)==c['input_sha256'] and sha(dst)==c['output_sha256'],'translation hash')
    shifts=dict(c['shifts']);need(len(shifts)==len(c['shifts']),'duplicate shift')
    e=copy.deepcopy(src);e.pop('metrics',None);e.pop('elimination',None);e['variant']+=':integral_translation'
    if 'search_history' in c:e['variant']+=':finite_centering'
    for row in e['residuals']:
        p=norm(row)
        for i,s in shifts.items():need(type(s) is int and 0<=i<len(e['variables']),'nonintegral translation');p=sub(p,i,add(v(i),con(s)))
        row['terms']=terms(p)
    need(e==dst,'literal translation mismatch')
    return len(shifts)

def natural_case(path):
    src=get(path/'raw/equation.json');dst=get(path/'natural/equation.json');cert=get(path/'natural/elimination_certificate.json')
    n=projection(src,dst,cert,True);poly,used=literal(dst);need(norm(get(path/'natural/expanded_polynomial.json'))==poly,'natural expanded polynomial')
    need(used==set(range(len(dst['variables']))) and deg(poly)==4,'natural degree or live census')
    return {'variables':len(dst['variables']),'rows':len(dst['residuals']),'monomials':len(poly),'height':max(map(abs,poly.values())),'projection_steps':n,'equation_sha256':sha(dst)}

def bundle(path,rawpath):
    names=['source','guarded','pruned_source','pruning_certificate','transform_certificate','factored_source','factorization_certificate','projected','projection_certificate','translation_certificate','equation','expanded_polynomial','METRICS']
    d={name:get(path/(name+'.json')) for name in names};d['raw']=get(rawpath/'raw_audit_input.json');d['original']=get(rawpath/'equation.json');
    if (path/'positive_seed_certificate.json').exists():d['positive_seed_certificate']=get(path/'positive_seed_certificate.json')
    return d

def check(d):
    c=d['transform_certificate'];
    if 'positive_seed_certificate' in d:seed_positivity(d['raw'],d['source'],d['positive_seed_certificate'])
    source_transform(d['raw'],d['original'],d['source'],c);g=domain(d['source'],d['guarded'],c)
    pruning(d['guarded'],d['pruned_source'],d['pruning_certificate'],c['seeds'])
    f=factorization(d['pruned_source'],d['factored_source'],d['factorization_certificate']);p=projection(d['factored_source'],d['projected'],d['projection_certificate']);t=translation(d['projected'],d['equation'],d['translation_certificate'])
    poly,used=literal(d['equation']);need(poly==norm(d['expanded_polynomial']),'expanded polynomial mismatch');need(deg(poly)==4,'not quartic');need(used==set(range(len(d['equation']['variables']))),'unused final coordinate')
    metrics={'variables':len(d['equation']['variables']),'rows':len(d['equation']['residuals']),'degree':deg(poly),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in d['equation']['residuals'] for c,m in r['terms']),'guards':g,'doubled_seeds':len(c['seeds']),'residue_one_guards':sum(o['kind']=='residue_one' for o in c['orientation']),'pair_fusions':len(c['paired_guards']),'reparameterized_remainders':sum(o['kind']=='residue_reparameterization' for o in c['orientation'])}
    need(all(d['METRICS'][k]==v for k,v in metrics.items()),'published metrics mismatch')
    return metrics|{'factorization_edits':f,'projection_steps':p,'integral_translations':t,'equation_sha256':sha(d['equation']),'polynomial_sha256':sha(d['expanded_polynomial'])}

def mutations(d):
    result={}
    def trial(name,fn):
        x=copy.deepcopy(d);fn(x)
        try:check(x)
        except (ValueError,KeyError,IndexError,TypeError) as err:result[name]={'rejected':True,'reason':str(err)}
        else:raise ValueError('Mutation survived: '+name)
    trial('expanded_coefficient',lambda x:x['expanded_polynomial']['terms'][0].__setitem__(0,x['expanded_polynomial']['terms'][0][0]+1))
    trial('projection_restoration',lambda x:x['projection_certificate']['steps'][0]['restoration'][0].__setitem__(0,2))
    trial('translation_shift',lambda x:x['translation_certificate']['shifts'][0].__setitem__(1,-2))
    trial('seed_selection',lambda x:x['transform_certificate']['selected_calls'].pop())
    trial('nonpositive_common_V_guard',lambda x:x['transform_certificate']['guards'][next(i for i,g in enumerate(x['transform_certificate']['guards']) if g['kind']=='positive_common_V')]['expression'].__setitem__(0,[0,[]]))
    trial('pair_anchor',lambda x:x['transform_certificate']['paired_guards'][0]['anchor'].__setitem__(0,x['transform_certificate']['paired_guards'][0]['pair'][0]))
    trial('sign_proof_rhs',lambda x:x['transform_certificate']['sign_inference']['proof_steps'][0]['rhs'][0].__setitem__(0,999))
    trial('frame_atom',lambda x:x['transform_certificate']['square_budget']['atoms'].pop())
    trial('factor_square_root',lambda x:next(iter(x['factorization_certificate']['square_roots'].values()))[0].__setitem__(0,999))
    trial('remainder_residue_constant',lambda x:next(o for o in x['transform_certificate']['orientation'] if o['kind']=='residue_reparameterization')['old_remainder'][0].__setitem__(0,2))
    trial('semantic_sign_interface',lambda x:x['transform_certificate']['sign_inference']['semantic_required'].pop())
    trial('private_slack_restoration',lambda x:x['pruning_certificate']['dropped_private_slacks'][0]['restoration'][0].__setitem__(0,999))
    if 'positive_seed_certificate' in d:trial('seed_lower_bound',lambda x:x['positive_seed_certificate']['seeds'][0].__setitem__('lower_bound',0))
    trial('metric_height',lambda x:x['METRICS'].__setitem__('height',1))
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--variant',default='unified_reparam_shell');ap.add_argument('--raw',default='unified_slack_shell');ap.add_argument('--endpoint');ap.add_argument('--output',type=Path);ap.add_argument('--skip-natural',action='store_true');args=ap.parse_args()
    d=bundle(ROOT/'direct'/args.variant,ROOT/'architecture'/args.raw/'raw')
    source_receipt=check(d)
    if args.endpoint:
        endpoint=ROOT/'direct'/args.endpoint
        newcert=get(endpoint/'translation_certificate.json')
        need(newcert['source_translation_sha256']==sha(d['translation_certificate']),'centering parent translation binding')
        need(get(endpoint/'projected.json')==d['projected'],'centering projected parent mismatch')
        for name in ['equation','expanded_polynomial','translation_certificate']:d[name]=get(endpoint/(name+'.json'))
        d['METRICS'].update(get(endpoint/'METRICS.json'))
    result={'verified':True,'source_receipt':source_receipt,'signed':check(d),'mutation_controls':mutations(d),'scope':'Exact literal certificate replay, not a formal proof of the arithmetic theorem or a consistency decision.'}
    if not args.skip_natural:result['natural']={name:natural_case(ROOT/'architecture'/name) for name in ['unified_derived_cantor','unified_slack_shell','unified_square_derived_cantor','unified_square_slack_shell','unified_derived_shell','unified_slack_cantor']}
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
