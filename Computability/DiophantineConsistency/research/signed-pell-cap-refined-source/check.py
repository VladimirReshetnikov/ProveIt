#!/usr/bin/env python3
"""Stdlib-only complete refined SOURCE audit; execution remains on review HOLD."""
import argparse,copy,hashlib,json,sys
from collections import Counter
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/signed-pell-cap-source'
LEGACY=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'
RAW=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/architecture/unified_derived_shell/raw/raw_audit_input.json'
SEALS={'research/signed-pell-cap-source':'53244a0a26bcfe2411c28adf2c6d74f7a4618c0c42c7904e8818be4e3f9a6ef5','research/signed-pell-cap-unoriented':'9fbb6fc816b0526bc16285c5198a2c7ffa179bdf4e1f9331fc83605d639e8be2','research/signed-pell-cap-factorial-output-guard':'e5c75ddaf0a8aebc23ced3b780122a15bbfdf317ea59e2457af32e755e0e0886','research/signed-pell-cap-helper-reflection':'77d184efa8282e84c68b3252bfd41bb9cecb31c4983fb2d0824dfd8c8d77a493'}
CHRONOLOGY=['normalize_helper','absolute_frame_and_nonzero_t','unoriented_cap_with_signed_targets','signed_A_q_support_at_t','same_t_base_one_safe_F_output','F_ge_one_and_restore_F_graph','unoriented_existence_to_fresh_positive_old_source']
def need(b,s):
    if not b:raise ValueError(s)
def get(p):return json.loads(p.read_bytes())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def encode(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def P(ts):
    d={}
    for c,m in ts:k=tuple(sorted(m));d[k]=d.get(k,0)+c
    return {m:c for m,c in d.items() if c}
def T(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def V(i):return {(i,):1}
def C(c):return {():c} if c else {}
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def sc(p,c):return {m:c*v for m,v in p.items() if c*v}
def mul(p,q):
    d={}
    for m,c in p.items():
        for n,b in q.items():k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*b
    return {m:c for m,c in d.items() if c}
def sub(p,i,q):
    out={}
    for m,c in p.items():
        term=C(c)
        for j in m:term=mul(term,q if i==j else V(j))
        out=add(out,term)
    return out
def remap(p,mapping):return {tuple(sorted(mapping[i] for i in m)):c for m,c in p.items()}
def equivalent(p,q):return p==q or p==sc(q,-1)
def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for section,base in [('files',ROOT),('core',HERE)]:
        for n,h in pins[section].items():need(digest(base/n)==h,'whole '+section+' '+n)
    for n,h in pins['closed_dependencies'].items():
        d=ROOT/n;need(digest(d/'MANIFEST.json')==h,'closed dependency '+n);need(get(d/'MANIFEST.json')['files']=={str(p.relative_to(d)):digest(p) for p in d.rglob('*') if p.is_file() and p!=d/'MANIFEST.json'},'whole closed packet '+n)
    need(all(pins['closed_dependencies'].get(n)==h for n,h in SEALS.items()),'all four exact ordinary/literal seals')
    if (HERE/'MANIFEST.json').exists():need(get(HERE/'MANIFEST.json')['files']=={str(p.relative_to(HERE)):digest(p) for p in HERE.rglob('*') if p.is_file() and p!=HERE/'MANIFEST.json'},'whole closed refined source')
def raw_expand(raw,source):
    names={v['name']:i for i,v in enumerate(source['variables'])};memo={};busy=set()
    def token(t):
        if t[0]=='c':return C(t[1])
        need(t[0]=='v','raw token type');i=t[1]
        if i in memo:return memo[i]
        name=raw['variables'][i]['name']
        if name in names:memo[i]=V(names[name]);return memo[i]
        need(i not in busy and str(i) in raw['gates'],'complete raw port definition');busy.add(i);p=P(raw['rows'][raw['gates'][str(i)]]['terms']);co=p.pop((i,),0);need(co in [-1,1] and not any(i in m for m in p),'actual monic raw port')
        out={}
        for m,c in p.items():
            value=C(-c//co)
            for j in m:value=mul(value,token(['v',j]))
            out=add(out,value)
        busy.remove(i);memo[i]=out;return out
    return token
def interfaces(raw,source):
    expand=raw_expand(raw,source);calls=[{k:T(expand(p[k])) for k in ['base','exponent','output']} for p in raw['powers']];atoms=[];seen=set();seeds=[]
    for p in raw['powers']:
        for k in ['base','exponent','output']:
            tok=p[k]
            if tuple(tok) not in seen:seen.add(tuple(tok));atoms.append(dict(token=tok,affine=T(expand(tok))))
    for s in raw['seeds']:
        pair=[next(iter(expand(t)))[0] for t in s['pair']];need(all(expand(t)==V(i) for t,i in zip(s['pair'],pair)),'literal independent pair coordinates');ids=[i for i,p in enumerate(raw['powers']) if p['exponent']==s['exponent']]
        seeds.append(dict(prefix=source['variables'][pair[0]]['name'].split('.')[0],pair=pair,target=T(expand(s['exponent'])),calls=ids))
    need(len(calls)==18 and len(seeds)==15 and len(atoms)==37,'complete original power/seed/frame interfaces')
    return calls,seeds,atoms
def expected(raw):
    body=get(PARENT/'source.json');old=get(PARENT/'guarded.json');domain=get(PARENT/'domain.json')['guards'];dropvars={396,397,398,408,409,410,480,481,482,483,484,485};droprows={217,337,361,362}
    oldkeep=[i for i in range(len(old['variables'])) if i not in dropvars];gm={i:j for j,i in enumerate(oldkeep)};oldrows=[i for i in range(len(old['residuals'])) if i not in droprows];rm={i:j for j,i in enumerate(oldrows)}
    bodykeep=[i for i in range(len(body['variables'])) if i not in {396,397,398}];bm={i:j for j,i in enumerate(bodykeep)};delta=mul(add(V(387),sc(V(245),-1)),add(V(387),sc(V(245),-1)))
    def row(i,r):return dict(label=r['label'],terms=T(remap(add(P(r['terms']),sc(delta,-1) if i==219 else {}),gm)))
    source=dict(schema='refined_signed_pell_cap_body_v1',domain='unrestricted integers',variant='unoriented_signed_cap_F_unrestricted_helper_base_guard_source_only',variables=[body['variables'][i] for i in bodykeep],residuals=[row(i,r) for i,r in enumerate(body['residuals']) if i!=217],polynomial='sum of squares of all residuals',parent_source_manifest_sha256=SEALS['research/signed-pell-cap-source'],ordinary_manifests_sha256={n:h for n,h in SEALS.items() if n!='research/signed-pell-cap-source'})
    guarded=copy.deepcopy(source);guarded['variables']=[old['variables'][i] for i in oldkeep];guarded['residuals']=[row(i,old['residuals'][i]) for i in oldrows];aux=list(range(len(oldkeep),len(oldkeep)+3));expr=add(V(gm[255]),C(-4));helper=dict(kind='comparison_base_lower',expression=T(expr),auxiliary=aux,row=len(oldrows),replaces_original_guard_indices=[27,30])
    guarded['variables'] += [dict(name='helper_base_lower.'+s,kind='integer_guard') for s in ['a','b','c']];a,b,c=aux;guarded['residuals'].append(dict(label='domain_guard.helper_base_lower',terms=T(add(expr,{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}))))
    kept=[];removed=[]
    for g in domain:
        if g['row'] in droprows:removed.append(copy.deepcopy(g));continue
        q=copy.deepcopy(g);q['expression']=T(remap(P(g['expression']),gm));q['auxiliary']=[gm[i] for i in g['auxiliary']];q['row']=rm[g['row']]
        if 'coordinate' in g:q['coordinate']=gm[g['coordinate']]
        if 'pair' in g:q['pair']=[gm[i] for i in g['pair']]
        kept.append(q)
    kept.append(helper);calls,seeds,atoms=interfaces(raw,source);reflection={str(bm[i]):T(remap(p,bm)) for i,p in [(251,sc(V(251),-1)),(252,add(C(-2),sc(V(252),-1))),(254,sc(V(254),-1)),(375,add(C(-2),sc(V(375),-1)))]}
    plan=dict(schema='refined_signed_cap_source_literal_map_v1',parent_manifest_sha256=SEALS['research/signed-pell-cap-source'],ordinary_manifests_sha256=source['ordinary_manifests_sha256'],old_body_to_new=[[i,bm[i]] for i in bodykeep],old_guarded_to_new=[[i,gm[i]] for i in oldkeep],old_row_to_new=[dict(old_row=i,new_row=rm.get(i),status=('removed_graph' if i in droprows else 'primary_pool_cap_term_removed' if i==219 else 'retained')) for i in range(len(old['residuals']))],removed_private_coordinates=sorted(dropvars),removed_graphs=removed,new_helper_graph=helper,all_original_seeds=seeds,all37_frame_atoms=atoms,all18_power_calls=calls,reflection=reflection,chronology=CHRONOLOGY,native_front_old=list(range(246))+list(range(376,386)),native_front_new=[bm[i] for i in list(range(246))+list(range(376,386))],pool_quotient_transfer='At an old cap-source zero, h_new=h_old-(C-W)^2/(A-1); integrality follows from the accepted old cap theorem. Soundness reconstructs a fresh positive private Pell tuple after signed-A t-only F recovery.',old_whole_body_identity_claimed=False,A_positive_assumed_before_F=False,all_target_positivity_used_before_F=False,source_only=True,optimizer_factorization_projection_executed=False,accepted_frontier_claim=False)
    return {'source.json':source,'guarded.json':guarded,'domain.json':dict(schema='refined_signed_cap_source_domain_v1',guards=kept),'TRANSFORM.json':plan},body,old,bm,gm,rm,calls,seeds,atoms
def reflection_checks(source,domain,bm,rm):
    images={bm[251]:sc(V(bm[251]),-1),bm[252]:add(C(-2),sc(V(bm[252]),-1)),bm[254]:sc(V(bm[254]),-1),bm[375]:add(C(-2),sc(V(bm[375]),-1))}
    def apply(p):
        for i,q in images.items():p=sub(p,i,q)
        return p
    for i in range(len(source['variables'])):need(apply(apply(V(i)))==V(i),'complete helper involution')
    signs={rm[205]:-1,rm[323]:-1}
    for i,r in enumerate(source['residuals']):need(apply(P(r['terms']))==sc(P(r['terms']),signs.get(i,1)),'every complete refined body reflection identity')
    for g in domain['guards']:need(apply(P(g['expression']))==P(g['expression']),'all retained and new graph expressions reflection invariant')
    for old,hits in [(251,[205,206,207,323]),(252,[207]),(254,[205,206]),(375,[323])]:need([i for i,r in enumerate(source['residuals']) if any(bm[old] in m for c,m in r['terms'])]==[rm[i] for i in hits],'complete four-port occurrence ledger')
    constructor=add(V(bm[255]),sc(V(bm[251]),-4),sc(mul(V(bm[251]),V(bm[252])),-4));need(P(source['residuals'][rm[207]]['terms'])==constructor,'new helper lower graph licenses normalization before any cap/F interpretation')
    need(any(g['kind']=='comparison_base_lower' and P(g['expression'])==add(V(bm[255]),C(-4)) for g in domain['guards']),'exact Bpart>=4 graph')
    return dict(all_body_row_identities=True,all_coordinate_involutions=True,all_retained_graphs_fixed=True,normalization_precedes_cap_and_F=True,normalized_old_signs=['V>=1','d>=0'],arbitrary_input_helper_sign_assumed=False)
def staged_signs(source,domain,bm,rm):
    legacy=get(LEGACY/'transform_certificate.json');parent=get(PARENT/'TRANSFORM.json');rawmap={i:bm[j] for i,j in parent['raw_to_body'] if j in bm};oldrowmap=parent['complete_old_row_map']
    scalar={g['coordinate'] for g in domain['guards'] if g['kind']=='nonnegative'};need(bm[3] not in scalar and {bm[i] for i in [0,7,8,185,247]}<=scalar,'exact F-free direct t/r/s/o/Z premises')
    need(all(g['kind']!='nonnegative' or P(g['expression'])==V(g['coordinate']) for g in domain['guards']),'each actual scalar expression')
    row=lambda i:P(source['residuals'][rm[i]]['terms'])
    need(row(3)==add(V(bm[5]),sc(V(bm[7]),-1),sc(V(bm[8]),-1),C(-1)) and row(167)==add(V(bm[179]),sc(V(bm[5]),-1),sc(V(bm[185]),-1),C(-1)),'raw B>=1/q>=2 before F')
    # V,d are licensed only at the normalized zero established above.
    initial=scalar|{bm[i] for i in [5,179,245,251,252]};pairs=[]
    for p in legacy['paired_guards']:
        u,s=(rawmap[i] for i in p['pair']);a,b=(rawmap[i] for i in p['anchor']);need({a,b}<=initial,'direct weighted anchor independent of F')
        need(any(g['kind']=='paired_interval' and g['pair']==[u,s] and P(g['expression'])==mul(V(u),V(s)) for g in domain['guards']),'literal retained weighted graph')
        ar=oldrowmap[p['anchor_row']]['new_row'];pr=oldrowmap[p['row']]['new_row'];need(add(row(ar),sc(row(pr),-1))==add(mul(V(bm[179]),add(V(u),sc(V(a),-1))),V(s),sc(V(b),-1)),'whole weighted pair identity');initial|={u,s};pairs.append([u,s])
    steps=[];skipped=[]
    for s in legacy['sign_inference']['proof_steps']:
        old=oldrowmap[s['row']]
        if old['status']!='retained':skipped.append(s['row']);continue
        v=rawmap[s['variable']];rhs=remap(P(s['rhs']),rawmap);deps={rawmap[j] for j in s['dependencies']};co=s['coefficient'];need(co>0 and equivalent(row(old['new_row']),add(sc(V(v),co),sc(rhs,-1))),'entire deferred retained sign identity')
        if s['kind']=='positive_monomials':need(all(c>0 for c in rhs.values()) and deps=={j for m in rhs for j,n in Counter(m).items() if n%2},'exact deferred positive-factor dependencies')
        else:need(s['kind']=='affine_square' and not deps and all(len(m)<=1 for m in P(s['square_root'])) and mul(remap(P(s['square_root']),rawmap),remap(P(s['square_root']),rawmap))==rhs,'exact deferred affine-square identity')
        steps.append((v,deps))
    def closure(seed):
        known=set(seed);changed=True
        while changed:
            changed=False
            for v,deps in steps:
                if deps<=known and v not in known:known.add(v);changed=True
        return known
    early=closure(initial);need({bm[i] for i in [0,4,5,7,8,179,185,245,247,251,252]}<=early,'all t-only raw/frame premises reachable without the F graph')
    later=closure(early|{bm[3]});required={rawmap[i] for i in legacy['sign_inference']['semantic_required'] if i not in {246,261,278}};need(required<=later,'full old native ledger only AFTER signed-A t recovery and fresh F graph')
    need(row(10)==add(V(bm[25]),C(-18),*[sc(V(bm[i]),-1) for i in [0,1,2,3]]),'actual later K bound');bounds={i:0 for i in later};bounds[bm[25]]=18;target_bounds=[]
    for s in interfaces(get(RAW),source)[1]:
        p=P(s['target']);need(all(c>0 and len(m)<=1 and all(i in bounds for i in m) for m,c in p.items()),'later affine original target bound');lower=sum(c*(bounds[m[0]] if m else 1) for m,c in p.items());need(lower>=1,'strict target bounds after F');target_bounds.append(dict(prefix=s['prefix'],lower_bound=lower))
    return dict(verified_retained_identities=len(steps),skipped_legacy_rows=skipped,pre_F_known=sorted(early),pre_F_direct_scalar_premises=sorted(scalar),pre_F_F_graph_assumed=False,pre_F_all_target_positivity_used=False,pre_F_helper_signs_only_after_normalization=True,post_F_required_targets=sorted(required),post_F_known=sorted(later),post_F_target_bounds=target_bounds)
def macro_interfaces(source,bm,rm,calls,seeds):
    definitions={};names={v['name']:i for i,v in enumerate(source['variables'])};capdefs={'index_cap.AY','index_cap.Y2','index_cap.BR'}
    for i,v in enumerate(source['variables']):
        special=v['name']=='index_addition.D';cap=v['name'] in capdefs
        if v['kind']!='gate' and not special and not cap:continue
        labels=['index_addition.D_definition'] if special else [v['name']] if cap else ['addition','multiplication'];found=[]
        for r in source['residuals']:
            if r['label'] not in labels:continue
            p=P(r['terms']);co=p.get((i,),0)
            if (co in [-1,1] if special else co==1) and not any(i in m for m in p if m!=(i,)):found.append((co,p))
        if len(found)==1:definitions[i]=found[0]
    boundary={bm[i] for i in list(range(246))+list(range(376,386))+[246,247,250,251,252,253,255,375,386,387,390,391,393,394,395]}|{j for s in seeds for j in s['pair']}|{i for i,v in enumerate(source['variables']) if v['name'].startswith('pow') and v['name'].endswith('.quotient')}|{names['base'+str(i)+'.T'] for i in range(5)}
    def expand(p,stop=boundary):
        memo={};busy=set()
        def value(i):
            if i in stop:return V(i)
            if i in memo:return memo[i]
            need(i in definitions and i not in busy,'complete acyclic literal macro gate '+str(i));busy.add(i);co,q=definitions[i];memo[i]=walk(sc(add(q,sc(V(i),-co)),-1//co));busy.remove(i);return memo[i]
        def walk(p):
            out={}
            for m,c in p.items():
                term=C(c)
                for i in m:term=mul(term,value(i))
                out=add(out,term)
            return out
        return walk(p)
    A=V(bm[246]);D=add(mul(A,A),C(-1));normcuts=[]
    for s in seeds:
        r=next(r for r in source['residuals'] if r['label']==s['prefix']+'.norm1');x,y=map(V,s['pair']);need(expand(P(r['terms']))==add(mul(x,x),sc(mul(D,mul(y,y)),-1),C(-1)),'every full original principal norm');normcuts.append(s['prefix'])
    for call,p in enumerate(calls):
        r=next(r for r in source['residuals'] if r['label']==f'pow{call}.power_congruence');d=V(names[f'pow{call}.quotient']);n=P(p['base'])
        if call==6:X,Y=map(V,seeds[0]['pair']);x=add(mul(A,X),mul(D,Y));y=add(X,mul(A,Y))
        else:s=next(s for s in seeds if call in s['calls']);x,y=map(V,s['pair'])
        group=next(i for i,first in enumerate([0,1,2,3,4]) if P(calls[first]['base'])==n);modulus=V(names['base'+str(group)+'.T']);need(expand(P(r['terms']))==add(x,mul(add(n,sc(A,-1)),y),sc(P(p['output']),-1),sc(mul(modulus,d),-1)),'every actual unsquared signed-A request')
    for i,first in enumerate([0,1,2,3,4]):
        r=next(r for r in source['residuals'] if r['label']=='base'+str(i)+'.T_definition');n=P(calls[first]['base']);want=add(sc(V(names['base'+str(i)+'.T']),-1),sc(mul(A,n),2),sc(mul(n,n),-1),C(-1));need(expand(P(r['terms']),boundary-{bm[175]})==want,'all five shared T definitions')
    for label,x,y,base in [('index_cap.norm',V(bm[386]),V(bm[387]),A),('index_cap.comparison_norm',V(bm[390]),V(bm[391]),add(V(bm[255]),C(1))),('shared_index.common_norm',V(bm[250]),V(bm[251]),A)]:
        r=source['residuals'][rm[206]] if label=='shared_index.common_norm' else next(r for r in source['residuals'] if r['label']==label);want=add(mul(x,x),sc(mul(add(mul(base,base),C(-1)),mul(y,y)),-1),C(-1));need(expand(P(r['terms']))==want,'complete unoriented anchor norm '+label)
    r=source['residuals'][rm[323]];cap2=mul(V(bm[387]),V(bm[387]));need(expand(P(r['terms']))==add(V(bm[251]),sc(cap2,-1),sc(mul(cap2,V(bm[375])),-1)),'full C squared common divisor')
    return dict(all15_norms=normcuts,all18_unsquared_power_calls=True,all5_shared_T_definitions=True,signed_t_plus_one_recurrence=True,all3_absolute_anchor_norms=True,C_squared_divisor=True)
def signed_power_identities():
    A,n,X,Y=map(V,range(4));D=add(mul(A,A),C(-1));mod=add(sc(mul(A,n),2),sc(mul(n,n),-1),C(-1));H=add(X,mul(add(n,sc(A,-1)),Y));J=add(X,sc(mul(add(n,sc(A,-1)),Y),-1));norm=add(mul(X,X),sc(mul(D,mul(Y,Y)),-1),C(-1))
    need(add(mul(H,J),C(-1),sc(mul(mod,mul(Y,Y)),-1))==norm,'whole signed-A branch product identity')
    xp=add(mul(A,X),mul(D,Y));yp=add(X,mul(A,Y));nextH=add(xp,mul(add(n,sc(A,-1)),yp));need(add(nextH,sc(mul(n,H),-1),sc(mul(mod,Y),-1))=={},'whole signed-A power recurrence identity')
    return dict(branch_product_and_recurrence_hold_for_every_integer_A=True,negative_canonical_abscissa_allowed=True,base_one_uses_same_pair_after_q_orientation=True,old_positive_A_power_lemma_used_before_F=False)
def validate(artifacts,raw):
    exp,oldbody,old,bm,gm,rm,calls,seeds,atoms=expected(raw);need(set(artifacts)==set(exp),'complete four-artifact inventory')
    for n,x in exp.items():need(artifacts[n]==x,'entire literal refined artifact '+n)
    source=artifacts['source.json'];guarded=artifacts['guarded.json'];domain=artifacts['domain.json'];plan=artifacts['TRANSFORM.json'];rows=source['residuals'];getrow=lambda i:P(rows[rm[i]]['terms'])
    need(source['domain']==guarded['domain']=='unrestricted integers' and len({v['name'] for v in guarded['variables']})==len(guarded['variables']),'full integer domain and unique names')
    used={i for r in guarded['residuals'] for c,m in r['terms'] for i in m};need(used==set(range(len(guarded['variables']))),'every guarded coordinate occurs')
    need(all(type(c) is int and len(m)<=2 and all(type(i) is int and 0<=i<len(guarded['variables']) for i in m) for r in guarded['residuals'] for c,m in r['terms']),'whole finite quadratic integer residual list')
    for g in plan['removed_graphs']:
        for v in g['auxiliary']:need([i for i,r in enumerate(old['residuals']) if any(v in m for c,m in r['terms'])]==[g['row']],'every removed old graph auxiliary is private')
    need({g['row'] for g in plan['removed_graphs']}=={217,337,361,362},'only the exact four old graphs omitted')
    for g in domain['guards']:
        a,b,c=g['auxiliary'];want=add(P(g['expression']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1});need(P(guarded['residuals'][g['row']]['terms'])==want,'every complete retained/new Legendre graph')
        for v in g['auxiliary']:need([i for i,r in enumerate(guarded['residuals']) if any(v in m for co,m in r['terms'])]==[g['row']],'every retained/new graph auxiliary is private')
    need(not any(g['kind']=='cap_lower' or g.get('original_guard_index') in {2,27,30} for g in domain['guards']),'no removed graph accidentally retained')
    need(all(getrow(i)==remap(P(oldbody['residuals'][i]['terms']),bm) for i in list(range(202))+list(range(324,335))),'entire unchanged noncontiguous native/front rows')
    Ccap,W,A,h=(V(bm[i]) for i in [387,245,246,395]);pool=add(*[mul(add(V(s['pair'][1]),sc(P(s['target']),-1)),add(V(s['pair'][1]),sc(P(s['target']),-1))) for s in seeds],sc(mul(A,h),-1),h)
    need(getrow(219)==pool and bm[387] not in {i for m in pool for i in m} and bm[245] not in {i for m in pool for i in m},'whole primary-only signed pool without cap terms')
    need(add(remap(P(oldbody['residuals'][219]['terms']),bm),sc(pool,-1))==mul(add(Ccap,sc(W,-1)),add(Ccap,sc(W,-1))),'exact old/new pool offset for h reset')
    need([i for i,r in enumerate(guarded['residuals']) if any(bm[395] in m for c,m in r['terms'])]==[rm[219]],'signed pool quotient has no other occurrence')
    a,b,c=[bm[i] for i in [399,400,401]];bound=add(mul(Ccap,Ccap),C(-1),*[sc(mul(V(s['pair'][1]),V(s['pair'][1])),-1) for s in seeds],{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1});need(getrow(218)==bound,'entire retained squared-cap graph')
    front=set(plan['native_front_new']);need(all(len(m)<=1 and all(i in front for i in m) for a in atoms for co,m in a['affine']),'all37 semantic atoms independent of cap/helper witnesses')
    frame=add(W,C(-4),*[sc(mul(P(a['affine']),P(a['affine'])),-2) for a in atoms]);need(getrow(334)==frame,'entire signed even square frame')
    membership=[]
    for j,p in enumerate(calls):
        for key in ['base','exponent','output']:need(any(P(p[key])==P(a['affine']) for a in atoms),'each of54 signed semantic power-port occurrences is bounded');membership.append([j,key])
    z=add(V(bm[247]),C(1));u=mul(W,z);v=mul(add(W,C(1)),u)
    need(getrow(202)==add(V(bm[248]),sc(u,-1)) and getrow(203)==add(V(bm[249]),sc(mul(add(W,C(1)),V(bm[248])),-1)),'full scale defining gates')
    scale=sub(sub(getrow(204),bm[249],v),bm[248],u);want=add(mul(A,A),sc(mul(mul(mul(W,W),W),mul(add(W,C(2)),mul(z,z))),-1),C(-1));need(scale==want,'full absolute-A scale norm before F')
    ceiling=add(getrow(1),getrow(2),sc(getrow(3),-1));need(ceiling==add(V(bm[6]),V(bm[8]),sc(mul(V(bm[3]),V(bm[5])),-1)),'exact t-only F ceiling combination')
    need(getrow(0)==add(V(bm[4]),sc(mul(V(bm[3]),V(bm[3])),-1)),'rho=F squared without an F sign')
    need(seeds[0]['calls']==[0,4] and P(calls[4]['base'])==V(bm[179]) and P(calls[4]['exponent'])==P(calls[0]['exponent'])==add(C(16),V(bm[0])) and P(calls[0]['base'])==add(C(1),V(bm[4])),'literal SAME-t support/base-one chronology')
    reflection=reflection_checks(source,domain,bm,rm);ledger=staged_signs(source,domain,bm,rm);macros=macro_interfaces(source,bm,rm,calls,seeds)
    return dict(whole_artifacts=True,whole_retained_rows_and_graphs=True,whole_private_occurrences=True,helper_normalization=reflection,full37_frame_atoms=atoms,all54_port_memberships=membership,all15_signed_targets=seeds,macro_interfaces=macros,signed_A_power_identities=signed_power_identities(),staged_sign_ledger=ledger,pre_F_t_lower_bound=16,pre_F_W_lower_bound=516,all_other_targets_may_be_signed_before_F=True,chronology=CHRONOLOGY,old_whole_body_identity_claimed=False,source_acceptance_or_frontier_claim=False)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--packet',type=Path,default=HERE);p.add_argument('--output',type=Path,required=True);a=p.parse_args();authenticate();raw=get(RAW);names=['source.json','guarded.json','domain.json','TRANSFORM.json'];artifacts={n:get(a.packet/n) for n in names};evidence=validate(artifacts,raw);controls=[]
    def trial(label,fn):
        d=copy.deepcopy(artifacts);fn(d)
        try:validate(d,raw)
        except (ValueError,KeyError,TypeError,IndexError,StopIteration):controls.append(label)
        else:raise ValueError('actual corruption accepted '+label)
    def row_change(d,label):next(r for r in d['source.json']['residuals'] if r['label']==label)['terms'][0][0]+=1
    for label in ['index_cap.joint_residue','index_cap.square_bound_guard','index_cap.norm','index_cap.comparison_norm','index_cap.R_mod_4Y','shared_index.V_positive_cap_square','shared.frame_definition','shared.last_norm','pow0.power_congruence','pow4.power_congruence','pow6.power_congruence','base0.T_definition','base4.T_definition']:
        trial('actual row '+label,lambda d,label=label:row_change(d,label))
    trial('wrong new helper threshold',lambda d:next(g for g in d['domain.json']['guards'] if g['kind']=='comparison_base_lower')['expression'][0].__setitem__(0,-3))
    trial('remaining guard altered',lambda d:d['guarded.json']['residuals'][-1]['terms'][0].__setitem__(0,999))
    trial('removed old graph privacy',lambda d:d['TRANSFORM.json']['removed_graphs'][0]['auxiliary'].pop())
    trial('missing guarded coordinate map',lambda d:d['TRANSFORM.json']['old_guarded_to_new'].pop())
    trial('missing retained native front',lambda d:d['TRANSFORM.json']['native_front_old'].pop())
    trial('wrong helper quotient reflection',lambda d:d['TRANSFORM.json']['reflection']['375'][0].__setitem__(0,0))
    trial('premature A orientation',lambda d:d['TRANSFORM.json'].__setitem__('A_positive_assumed_before_F',True))
    trial('premature all-target positivity',lambda d:d['TRANSFORM.json'].__setitem__('all_target_positivity_used_before_F',True))
    trial('helper normalization after F',lambda d:d['TRANSFORM.json']['chronology'].reverse())
    trial('false pointwise whole-body identity',lambda d:d['TRANSFORM.json'].__setitem__('old_whole_body_identity_claimed',True))
    trial('wrong unrestricted domain',lambda d:d['guarded.json'].__setitem__('domain','nonnegative integers'))
    trial('wrong signed target',lambda d:d['TRANSFORM.json']['all_original_seeds'][0]['target'][0].__setitem__(0,15))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_only=True,checker_sha256=digest(Path(__file__)),source_pins_sha256=digest(HERE/'SOURCE_PINS.json'),generated_sha256={n:digest(a.packet/n) for n in names},evidence=evidence,rejected_actual_artifacts=controls,producer_parent_optimizer_executed=False,scope='Complete combined ordinary-source interface and exact literal identities only. No optimizer, factorization, projection, collected quartic or frontier claim.')
    data=encode(result);need(not a.output.exists() or a.output.read_bytes()==data,'refuse changed receipt overwrite');a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(data);print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_only=True,rejected_actual_artifacts=len(controls)),sort_keys=True))
if __name__=='__main__':main()
