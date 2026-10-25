#!/usr/bin/env python3
"""Independent literal audit of round16 signed-cap artifacts.

Imports the previous independent auditor, never a producing compiler. New cap,
source changes, guards, factorization, projection, translation, and full quartic
are checked from literal rows. This does not re-prove inherited calibration.
"""
from pathlib import Path
from collections import Counter
import argparse, copy, hashlib, json, re
import round15_independent_algebra as P
need,norm,terms,add,sc,mul,v,con,sub,deg,solved,equiv=P.need,P.norm,P.terms,P.add,P.sc,P.mul,P.v,P.con,P.sub,P.deg,P.solved,P.equivalent
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
DEFAULT_RAW=HERE/'portable_input'
BASELINE_SHA256={'equation.json':'6dac6beef0fbc724f244c85f1e17730b141e96cdaba1b11d9c6528c6a19a8442','raw_audit_input.json':'f6602525ef57be22d2b5e8407efd4e000ec9be8b242eb2d0024dc757e2c1f587'}

def load_bundle(path,rawpath):
    for filename,pin in BASELINE_SHA256.items():need(hashlib.sha256((rawpath/filename).read_bytes()).hexdigest()==pin,'pinned baseline bytes mismatch: '+filename)
    names=['source','guarded','transform_certificate','factored_source','factorization_certificate','projected','projection_certificate','translation_certificate','equation','expanded_polynomial','METRICS']
    d={n:P.get(path/(n+'.json')) for n in names}
    d['original']=P.get(path/'input_equation.json') if (path/'input_equation.json').exists() else P.get(rawpath/'equation.json')
    d['raw']=P.get(path/'input_raw.json') if (path/'input_raw.json').exists() else P.get(rawpath/'raw_audit_input.json')
    baseline=P.get(rawpath/'equation.json');raw0=P.get(rawpath/'raw_audit_input.json')
    need(d['original']==baseline,'unbound baseline equation')
    if d['transform_certificate'].get('self_radix'):
        newraw=len(raw0['variables']);raw0['variables'].append({'name':'self_radix.BH','kind':'gate'});raw0['powers'][2]['base']=['v',newraw]
    if d['transform_certificate'].get('strict_budget'):
        oldk=raw0['powers'][1]['exponent'];oldx=raw0['powers'][14]['exponent'];rawx=['v',next(i for i,vv in enumerate(raw0['variables']) if vv['name']=='x')]
        for j in (1,2,14):raw0['powers'][j]['exponent']=rawx
        for field in ('seeds','indices'):
            raw0[field]=[sd for sd in raw0[field] if sd['exponent']!=oldk]
            for sd in raw0[field]:
                if sd['exponent']==oldx:sd['exponent']=rawx
        raw0['amplification']['K']=rawx;raw0['amplification']['budget']='x';raw0['amplification']['derived_label_radix_budget']='ell*(t+1)<2F<x=K'
        raw0['radix']['K']=rawx
        for rg in raw0['ranges']:
            if rg[3] in ('crt.range.u','crt.range.vq'):rg[1]=rawx
    need(d['raw']==raw0,'unapproved baseline raw metadata change')
    return d

def check_source(d):
    c,s,original,raw=(d[n] for n in ['transform_certificate','source','original','raw'])
    need(c['original_sha256']==P.sha(original) and c['raw_sha256']==P.sha(raw) and c['source_sha256']==P.sha(s),'source hash binding')
    need(original['domain']=='nonnegative integers' and s['domain']=='unrestricted integers','domain mismatch')
    names={x['name']:i for i,x in enumerate(s['variables'])}
    pre=copy.deepcopy(original)
    changes=c.get('architecture_changes',[])
    if c.get('self_radix'):
        base=names['self_radix.BH'];need(base==len(pre['variables']),'self radix base not fresh')
        pre['variables'].append({'name':'self_radix.BH','kind':'gate'})
        reps=[i for i,x in enumerate(original['variables']) if x['name'].startswith('crt.encoded.') or x['name']=='crt.encoded_index_minus_one']
        need(len(reps)==9,'self radix representative count')
        H=add(con(10),*[v(i) for i in reps]);B=v(names['choose0.output']);N=names['pow1.output']
        pre['residuals'].append({'label':'self_radix.base_definition','terms':terms(add(v(base),sc(mul(B,H),-1)))})
        allowed={}
        for ri,row in enumerate(pre['residuals']):
            p=norm(row)
            if row['label']=='base2.T_definition':
                allowed[ri]=add(p,v(names['mul.385']),sc(mul(v(base),v(base)),-1))
            elif row['label']=='multiplication' and any(N in mon and (names['shared.A'] in mon or names['index1.Y'] in mon) for mon in p):
                allowed[ri]=sub(p,N,v(base))
        need(len(allowed)==3,'self radix exact substitution inventory')
        seen=set()
        for ch in changes:
            if ch['kind']=='remove_aggregate' or ch['kind'].startswith('strict_'):continue
            need(ch['kind']=='self_radix_row' and ch['row'] in allowed,'unexpected architecture edit')
            ri=ch['row'];need(ri not in seen and ch['old']==pre['residuals'][ri] and norm(ch['new'])==allowed[ri],'wrong architecture edit');seen.add(ri);pre['residuals'][ri]=ch['new']
        need(seen==set(allowed),'missing self radix edit')
        old=[r for r in pre['residuals'] if r['label']=='crt.aggregate_representative_bound']
        need(len(old)==1 and [x for x in changes if x['kind']=='remove_aggregate']==[{'kind':'remove_aggregate','old':old[0]}],'aggregate removal mismatch')
        pre['residuals']=[r for r in pre['residuals'] if r['label']!='crt.aggregate_representative_bound']
        rb=raw['powers'][2]['base'];need(raw['variables'][rb[1]]['name']=='self_radix.BH','modified raw power base')
    else:need(not changes,'unrequested architecture changes')
    strictchanges=[ch for ch in changes if ch['kind'].startswith('strict_')]
    if c.get('strict_budget'):
        oldpair=[names['index1.X'],names['index1.Y']];newpair=[names['index12.X'],names['index12.Y']]
        def aywire(prefix):
            nr=norm(next(r for r in pre['residuals'] if r['label']==prefix+'.norm1'))
            return next(mon[0] for mon,coef in nr.items() if coef==-1 and len(mon)==2 and mon[0]==mon[1])
        olday=aywire('index1');neway=aywire('index12');aliases=dict(zip(oldpair+[olday],newpair+[neway]));kept=[];expectedstrict=[]
        for ri,rr in enumerate(pre['residuals']):
            p=norm(rr)
            if rr['label']=='index1.norm1' or equiv(p,add(v(olday),sc(mul(v(names['shared.A']),v(oldpair[1])),-1))):
                expectedstrict.append({'kind':'strict_delete','row':ri,'old':rr});continue
            pp=p
            for old,new in aliases.items():pp=sub(pp,old,v(new))
            nr=dict(rr,terms=terms(pp))
            if nr!=rr:expectedstrict.append({'kind':'strict_alias','row':ri,'old':rr,'new':nr})
            kept.append(nr)
        need(expectedstrict==strictchanges,'strict budget alias or deletion mismatch');pre['residuals']=kept
    else:need(not strictchanges,'unrequested strict budget change')
    calls,atom=P.square_budget(raw,pre,c['square_budget']);pre.pop('metrics',None);pre['domain']='unrestricted integers';pre['variant']+=':signed_pooled_cap'
    b=c['square_budget'];pre['residuals'][b['frame_row']]=b['new_frame']
    if c.get('cofinal'):
        root=names['cofinal.horizon_root'];need(root==len(pre['variables']),'cofinal coordinate freshness')
        pre['variables'].append({'name':'cofinal.horizon_root','kind':'signed_witness'})
        pre['residuals'] += [
          {'label':'cofinal.horizon','terms':terms(add(v(names['t0']),sc(mul(v(root),v(root)),-1)))},
          {'label':'cofinal.beta_base','terms':terms(add(v(names['y']),sc(mul(v(names['pow0.output']),v(names['pow0.output'])),-1),v(names['pow0.output'])))}]
    expected_seeds=[]
    for seed in raw['seeds']:
        ids=[j for j,p in enumerate(raw['powers']) if p['exponent']==seed['exponent']]
        pair=[names[raw['variables'][a[1]]['name']] for a in seed['pair']]
        expected_seeds.append({'pair':pair,'exponent':calls[ids[0]]['exponent'],'calls':ids})
    need(c['seed_data']==expected_seeds and len(expected_seeds)==(14 if c.get('strict_budget') else 15),'principal pair ledger mismatch')
    deleted=[{'row':i,'content':r} for i,r in enumerate(pre['residuals']) if re.fullmatch(r'index\d+\.(index_at_most_Y|norm3|S_mod_U|R_mod_4Y)',r['label']) or r['label'].startswith('shared_index.')]
    need(deleted==c['deleted_constraints'],'deleted constraint inventory')
    dead={x['row'] for x in deleted};pre['residuals']=[r for i,r in enumerate(pre['residuals']) if i not in dead]
    modifications=[]
    if c.get('odd_frame'):
        z=names['shared.Zminus1']
        for ri,row in enumerate(pre['residuals']):
            if any(z in m for m in norm(row)):
                new=dict(row,terms=terms(sub(norm(row),z,sc(v(z),2))))
                modifications.append({'row':ri,'old':row,'new':new});pre['residuals'][ri]=new
    need(modifications==c['modifications'],'odd frame substitution mismatch')
    need(pre['residuals']==s['residuals'][:len(pre['residuals'])],'retained source rows differ')
    need(pre['variables']==s['variables'][:len(pre['variables'])],'retained variables differ')
    cv=c['cap_variables'];need(set(cv)=={'U','Y','H','J','S','R','B','d','e','f','g','h'},'anchor variable inventory')
    for n,i in cv.items():
        if c.get('semantic_anchor') and n in ('U','Y'):need(i==expected_seeds[-1]['pair'][0 if n=='U' else 1],'reused anchor coordinate binding')
        else:need(names['cap.'+n]==i,'anchor coordinate binding')
    anchor_index=norm(expected_seeds[-1]['exponent']) if c.get('semantic_anchor') else v(names['shared.W'])
    need(norm(c['anchor_index'])==anchor_index,'anchor index binding')
    if c.get('signed_center'):need(c.get('squared_anchor'),'signed-center semantic anchor requires squared cap')
    W,A=v(names['shared.W']),v(names['shared.A']);U,Y,H,J,C,R,B,dd,e,f,g,h=[v(cv[n]) for n in ['U','Y','H','J','S','R','B','d','e','f','g','h']]
    expected=[]
    def row(n,p):expected.append({'label':'cap.'+n,'terms':terms(p)})
    normpairs=[('common',H,J)] if c.get('semantic_anchor') else [('main',U,Y),('common',H,J)]
    for label,x,y in normpairs:
        ay=v(names['cap.'+label+'_Ay']);row(label+'_Ay',add(ay,sc(mul(A,y),-1)));row(label+'_norm',add(mul(x,x),mul(y,y),sc(mul(ay,ay),-1),con(-1)))
    br=v(names['cap.BR']);row('BR',add(br,sc(mul(B,R),-1)));row('comparison_norm',add(mul(C,C),mul(R,R),sc(mul(br,br),-1),con(-1)))
    y2=v(c['cap_square_variable']);need(c['cap_square_variable']==names['cap.Y2'],'anchor square variable');row('Y2',add(y2,sc(mul(Y,Y),-1)))
    row('common_multiple',add(J,sc(mul(y2,add(sc(e,2 if c.get('odd_auxiliary') else 1),con(1))),-1)))
    factor=add(sc(dd,2),con(1)) if c.get('odd_comparison') else add(dd,con(1))
    row('comparison_constructor',add(B,con(-1),sc(mul(J,factor),-4)))
    row('comparison_modulus',add(B,sc(A,-1),sc(mul(H,f),-1)))
    row('abscissa_residue',add(C,sc(U,-1),sc(mul(H,g),-1)))
    row('index_residue',add(R,sc(anchor_index,-1),sc(mul(Y,h),-4)))
    pooled={}
    for sd in expected_seeds:
        x,y=map(v,sd['pair']);delta=add(y,sc(norm(sd['exponent']),-1));pooled=add(pooled,mul(delta,delta))
        if not c['ys_only']:pooled=add(pooled,mul(add(x,con(-1)),add(x,con(-1))))
    if c.get('sparse'):
        need(c['pooled_quotient'] is None,'sparse pooled variable')
        for i,sd in enumerate(expected_seeds):
            row('index_residue_'+str(i),add(v(sd['pair'][1]),sc(norm(sd['exponent']),-1),sc(mul(add(A,con(-1)),v(names['cap.residue_'+str(i)])),-1)))
            if not c['ys_only']:row('sign_residue_'+str(i),add(v(sd['pair'][0]),con(-1),sc(mul(add(A,con(-1)),v(names['cap.sign_residue_'+str(i)])),-1)))
    elif 'pooled_groups' not in c:row('pooled_index_residue',add(pooled,sc(mul(add(A,con(-1)),v(c['pooled_quotient'])),-1)))
    else:
        groups=[];width=c.get('pool_width') or len(expected_seeds)
        need(width>=1,'invalid pool width')
        for lo in range(0,len(expected_seeds),width):
            ids=list(range(lo,min(lo+width,len(expected_seeds))))
            kinds=['y','x'] if c.get('separate_sign_pool') and not c['ys_only'] else ['y' if c['ys_only'] else 'both']
            for kind in kinds:
                p={}
                for si in ids:
                    sd=expected_seeds[si];x,y=map(v,sd['pair'])
                    if kind in ('y','both'):
                        delta=add(y,sc(norm(sd['exponent']),-1));p=add(p,mul(delta,delta))
                    if kind in ('x','both'):p=add(p,mul(add(x,con(-1)),add(x,con(-1))))
                groups.append({'indices':ids,'kind':kind,'polynomial':terms(p)})
        for gi,group in enumerate(groups):
            suffix='' if len(groups)==1 else '_'+str(gi)
            qi=names['cap.pooled_quotient'+suffix];group['quotient']=qi
            row('pooled_index_residue'+suffix,add(norm(group['polynomial']),sc(mul(add(A,con(-1)),v(qi)),-1)))
        need(groups==c['pooled_groups'],'pooled group partition or formula mismatch')
        need(c['pooled_quotient']==(groups[0]['quotient'] if len(groups)==1 else None),'pooled quotient binding')
    need(s['residuals']==pre['residuals']+expected,'complete appended cap row mismatch')
    need(all(deg(norm(r))<=2 for r in s['residuals']),'source nonquadratic')
    # Bind each retained Pell norm and its original multiplication gate by exact identity.
    for sd in expected_seeds:
        xi,yi=sd['pair'];prefix=s['variables'][xi]['name'].rsplit('.',1)[0]
        nr=[norm(r) for r in s['residuals'] if r['label']==prefix+'.norm1'];need(len(nr)==1,'missing principal norm')
        other=add(nr[0],con(1),sc(v(xi),0),sc(mul(v(xi),v(xi)),-1),sc(mul(v(yi),v(yi)),-1))
        need(len(other)==1,'unexpected principal norm shape');((mon,coef),)=other.items();need(coef==-1 and len(mon)==2 and mon[0]==mon[1],'principal product-square shape');ay=mon[0]
        need(any(equiv(norm(r),add(v(ay),sc(mul(A,v(yi)),-1))) for r in s['residuals']),'principal A times Y gate missing')
    return calls

def check_guards(d):
    s,c,guarded=d['source'],d['transform_certificate'],d['guarded'];names={x['name']:i for i,x in enumerate(s['variables'])};W=c['square_budget']['frame_variable'];cv=c['cap_variables'];proof=c['sign_inference']
    expected=copy.deepcopy(s);front=set();pairs=[];extra={}
    allpairs=[]
    for ri,r in enumerate(s['residuals']):
        if not(r['label'].endswith('.remainder_bound') and r['label']!='fact0.remainder_bound'):continue
        pair=[m[0] for m,coef in norm(r).items() if len(m)==1 and coef==-1 and any(s['variables'][m[0]]['name'].endswith(z) for z in ['.remainder','.slack','.rslack'])]
        need(len(pair)==2,'interval coordinate extraction');allpairs.append({'row':ri,'pair':pair})
    need(c['pairs']==allpairs,'interval coverage')
    for j,g in enumerate(c['guards']):
        kind=g['kind']
        if kind=='front_nonnegative':expr=v(g['coordinate']);need(g['coordinate'] not in front,'duplicate front guard');front.add(g['coordinate'])
        elif kind=='postsemantic_interval':
            pair=g['pair'];expr=mul(v(pair[0]),v(pair[1]));need({'row':g['bound_row'],'pair':pair} in allpairs,'unbound product guard');pairs.append(pair)
        elif kind=='anchor_common_multiplier':expr=v(cv['e']);extra[kind]=extra.get(kind,0)+1
        elif kind=='anchor_index_bound':expr=add(v(cv['Y']),sc(v(W),-1));extra[kind]=extra.get(kind,0)+1
        elif kind=='anchor_comparison_multiplier':expr=v(cv['d']);extra[kind]=extra.get(kind,0)+1
        elif kind=='shared_square_cap':
            anchor_index=norm(c['anchor_index'])
            expr=add(mul(v(cv['Y']),v(cv['Y'])) if c.get('squared_anchor') else (v(cv['Y']) if c.get('strong_cap') else v(c['cap_square_variable'])),sc(mul(anchor_index,anchor_index),-1) if c.get('squared_anchor') else (sc(anchor_index,-1) if c.get('strong_cap') else {}),con(-1),*[sc(mul(v(sd['pair'][1]),v(sd['pair'][1])),-1) for i,sd in enumerate(c['seed_data']) if not(c.get('semantic_anchor') and i==len(c['seed_data'])-1)]);extra[kind]=extra.get(kind,0)+1
        else:raise ValueError('unknown guard '+kind)
        need(norm(g['expression'])==expr,'guard expression mismatch')
        aux=list(range(len(expected['variables']),len(expected['variables'])+3));need(g['auxiliary']==aux,'guard freshness');a,b,cc=aux
        expected['variables'] += [{'name':f'guard{j}.{z}','kind':'integer_guard'} for z in ['a','b','c']]
        need(g['row']==len(expected['residuals']),'guard index')
        expected['residuals'].append({'label':f'domain_guard.{j}','terms':terms(add(expr,{(a,a):-1,(b,b):-1,(cc,cc):-1,(cc,):-1}))})
    need(expected==guarded,'complete guarded literal mismatch')
    need(pairs==[p['pair'] for p in allpairs],'product guard exact coverage')
    want={'shared_square_cap':1}
    if not c.get('odd_auxiliary'):want['anchor_common_multiplier']=1
    if not c.get('strong_cap'):want['anchor_index_bound']=1
    if not c.get('odd_comparison'):want['anchor_comparison_multiplier']=1
    need(extra==want,'anchor guard inventory');need(front==set(proof['guard_indices']),'front guard inference mismatch')
    known=front|{W}
    for st in proof['proof_steps']:
        i,coef=st['variable'],st['coefficient'];rhs=norm(st['rhs']);rr=norm(s['residuals'][st['row']]);need(coef>0 and equiv(rr,add(sc(v(i),coef),sc(rhs,-1))),'nonnegative inference identity')
        if st['kind']=='positive_monomials':
            need(all(c>=0 for c in rhs.values()),'negative coefficient in monotone proof');deps={j for mon in rhs for j,power in Counter(mon).items() if power%2};need(deps==set(st['dependencies']) and deps<=known,'missing sign premise')
        else:
            need(st['kind']=='affine_square' and not st['dependencies'],'unknown sign rule');root=norm(st['square_root']);need(deg(root)<=1 and mul(root,root)==rhs,'bad square inference')
        known.add(i)
    need(known==set(proof['known_nonnegative']),'sign closure census');need(set(proof['semantic_required'])<=known,'sign interface uncovered')
    critical=['x','fact0.remainder','fact0.slack','choose0.oslack']+([] if c.get('signed_center') else ['shared.A'])+[x['name'] for x in s['variables'] if x['name'].startswith('crt.encoded.') or x['name']=='crt.encoded_index_minus_one']
    if c.get('orientation_first'):
        need(not c['ys_only'] and c.get('squared_anchor'),'invalid orientation-first source')
        critical=[n for n in critical if n!='x' and not n.startswith('crt.encoded')]
    if not c.get('cofinal'):critical+=['t0','endpoint.r0']
    for name in critical:need(names[name] in known,'missing bootstrap sign '+name)
    # Cofinal's horizon is independently a square; its y sign is an integer-product fact.
    if c.get('cofinal'):need(names['t0'] in known,'cofinal horizon not recovered as square')
    return len(c['guards'])

def check(d):
    calls=check_source(d);g=check_guards(d)
    f=P.factorization(d['guarded'],d['factored_source'],d['factorization_certificate'])
    pp=P.projection(d['factored_source'],d['projected'],d['projection_certificate'])
    t=P.translation(d['projected'],d['equation'],d['translation_certificate'])
    poly,used=P.literal(d['equation']);need(poly==norm(d['expanded_polynomial']),'expanded quartic mismatch');need(deg(poly)==4 and used==set(range(len(d['equation']['variables']))),'degree/live variable mismatch')
    metrics={'variables':len(d['equation']['variables']),'rows':len(d['equation']['residuals']),'degree':4,'monomials':len(poly),'height':max(map(abs,poly.values())),'guards':g,'main_pairs':len(d['transform_certificate']['seed_data'])}
    need(all(d['METRICS'][k]==val for k,val in metrics.items()),'metric mismatch')
    return metrics|{'factorization_edits':f,'projection_steps':pp,'integral_translations':t,'equation_sha256':P.sha(d['equation']),'source_sha256':P.sha(d['source']),'power_calls':len(calls),'A_nonnegative_retained':not d['transform_certificate'].get('signed_center'),'squared_anchor':d['transform_certificate'].get('squared_anchor'),'odd_auxiliary':d['transform_certificate'].get('odd_auxiliary'),'semantic_anchor':d['transform_certificate'].get('semantic_anchor')}

def mutation_controls(d):
    result={}
    def trial(name,edit):
        changed=copy.deepcopy(d);edit(changed)
        try:check(changed)
        except (ValueError,KeyError,IndexError,TypeError) as exc:result[name]={'rejected':True,'reason':str(exc)}
        else:raise ValueError('mutation accepted: '+name)
    def source_edit(z,label):
        row=next(r for r in z['source']['residuals'] if r['label']==label or (label=='cap.pooled_index_residue' and r['label'].startswith(label+'_')));row['terms'].append([1,[]]);z['transform_certificate']['source_sha256']=P.sha(z['source'])
    trial('omit_principal_seed',lambda z:z['transform_certificate']['seed_data'].pop())
    trial('drop_frame_atom',lambda z:z['transform_certificate']['square_budget']['atoms'].pop())
    trial('corrupt_anchor_norm_after_rehash',lambda z:source_edit(z,'cap.common_norm'))
    trial('corrupt_odd_constructor_after_rehash',lambda z:source_edit(z,'cap.comparison_constructor'))
    trial('corrupt_pooled_row_after_rehash',lambda z:source_edit(z,'cap.pooled_index_residue'))
    trial('omit_W_from_cap_guard',lambda z:next(g for g in z['transform_certificate']['guards'] if g['kind']=='shared_square_cap')['expression'].append([1,[z['transform_certificate']['square_budget']['frame_variable']]]))
    trial('corrupt_sign_inference',lambda z:z['transform_certificate']['sign_inference']['proof_steps'][0]['rhs'][0].__setitem__(0,999))
    trial('corrupt_projection_restoration',lambda z:z['projection_certificate']['steps'][0]['restoration'][0].__setitem__(0,999))
    trial('corrupt_factor_root',lambda z:next(iter(z['factorization_certificate']['square_roots'].values()))[0].__setitem__(0,999))
    trial('corrupt_translation',lambda z:z['translation_certificate']['shifts'][0].__setitem__(1,999))
    trial('corrupt_expanded_coefficient',lambda z:z['expanded_polynomial']['terms'][0].__setitem__(0,999))
    trial('corrupt_metrics',lambda z:z['METRICS'].__setitem__('height',1))
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('variants',nargs='+',type=Path);ap.add_argument('--raw',type=Path,default=DEFAULT_RAW);ap.add_argument('--output',type=Path);ap.add_argument('--centered',type=Path,nargs='*',default=[]);ap.add_argument('--adversarial',action='store_true');args=ap.parse_args()
    results={str(p):check(load_bundle(p,args.raw)) for p in args.variants}
    need(not args.centered or len(args.centered)==len(args.variants),'centered/source pairing')
    for source_path,end_path in zip(args.variants,args.centered):
        d=load_bundle(source_path,args.raw);cc=P.get(end_path/'translation_certificate.json')
        need(cc['source_translation_sha256']==P.sha(d['translation_certificate']),'centering parent translation mismatch')
        need(P.get(end_path/'projected.json')==d['projected'],'centering parent projected mismatch')
        for key in ['translation_certificate','equation','expanded_polynomial']:d[key]=P.get(end_path/(key+'.json'))
        d['METRICS'].update(P.get(end_path/'METRICS.json'));results[str(end_path)]=check(d)
    out={'status':'passed','scope':'Independent exact source/cap/domain/factorization/projection/translation/whole-quartic replay. Unbounded arithmetic and calibration remain separate proofs.','variants':results}
    if args.adversarial:out['mutation_controls']=mutation_controls(load_bundle(args.variants[0],args.raw))
    if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
