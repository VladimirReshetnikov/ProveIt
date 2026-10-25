#!/usr/bin/env python3
"""Optimizer-free complete literal/guard/frame audit of the source-only cap candidate."""
import argparse,json,sys
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'
RAW=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/architecture/unified_derived_shell/raw/raw_audit_input.json'
ORDINARY=ROOT/'research/signed-pell-cap'
SEAL='f5aefb843a055aa2de7151bd6fceab54288b7566b7bbd386dc5f4928fe7aa8c8'
PARENT_SHA='0b36a5ff088aece09f23dff8f55a2c6904e1f69615f16c4a5299acb1fa790c67'
SEEDS=[(0,257,258,[(16,[]),(1,[0])],[0,4]),(1,274,275,[(2,[25])],[1,2]),(2,296,297,[(16,[]),(1,[0]),(1,[4])],[3]),(3,319,320,[(1,[]),(1,[16])],[5]),(5,341,342,[(1,[]),(1,[17])],[7]),(6,355,356,[(1,[]),(1,[18])],[8]),(7,369,370,[(1,[]),(1,[19])],[9]),(8,383,384,[(1,[]),(1,[20])],[10]),(9,397,398,[(1,[]),(1,[2])],[11]),(10,411,412,[(1,[]),(1,[21])],[12]),(11,425,426,[(1,[]),(1,[22])],[13]),(12,439,440,[(1,[]),(1,[1])],[14]),(13,453,454,[(1,[]),(1,[23])],[15]),(14,467,468,[(1,[]),(1,[24])],[16]),(15,481,482,[(1,[]),(1,[171])],[17])]
DELETE_GROUPS=[[210,213,214,215,216,217,218],[225,228,229,230,231,232,233],[245,248,249,250,251,252,253],[266,269,270,271,272,273,274],[286,289,290,291,292,293,294],[298,301,302,303,304,305,306],[310,313,314,315,316,317,318],[322,325,326,327,328,329,330],[334,337,338,339,340,341,342],[346,349,350,351,352,353,354],[358,361,362,363,364,365,366],[370,373,374,375,376,377,378],[382,385,386,387,388,389,390],[394,397,398,399,400,401,402],[406,409,410,411,412,413,414]]
LINEAR={259:180,277:188,297:195,309:200,321:205,333:210,345:211,357:217,369:222,381:223,393:229,405:234,417:240}
CAP_NAMES=['X','Y','AY','Y2','S','R','BR','Squotient','Rquotient','pool_quotient','lower.a','lower.b','lower.c','bound.a','bound.b','bound.c']
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def encode(d):return (json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
def P(terms):
    out={}
    for c,m in terms:
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return {m:c for m,c in out.items() if c}
def T(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def C(c):return {():c} if c else {}
def V(i):return {(i,):1}
def plus(a,b,sgn=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+sgn*c
    return {m:c for m,c in out.items() if c}
def scale(a,c):return {m:c*v for m,v in a.items() if c*v}
def times(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def square(a):return times(a,a)
def total(*items):
    result={}
    for p in items:result=plus(result,p)
    return result
def rr(label,p):return dict(label=label,terms=T(p))
def move(p,mapping):
    out={}
    for m,c in p.items():
        k=tuple(sorted(mapping[j] for j in m));out[k]=out.get(k,0)+c
    return {m:c for m,c in out.items() if c}
def graph(p,a,b,c):return total(p,scale(square(V(a)),-1),scale(square(V(b)),-1),scale(square(V(c)),-1),scale(V(c),-1))
def authenticate():
    pins=load(HERE/'SOURCE_PINS.json');need(digest(ORDINARY/'MANIFEST.json')==SEAL and digest(PARENT/'source.json')==PARENT_SHA,'reviewed complete ordinary/source parents')
    manifest=load(ORDINARY/'MANIFEST.json')['files'];need(set(manifest)=={str(p.relative_to(ORDINARY)) for p in ORDINARY.rglob('*') if p.is_file() and p!=ORDINARY/'MANIFEST.json'},'closed ordinary source design')
    for n,h in manifest.items():need(digest(ORDINARY/n)==h,'whole ordinary member '+n)
    expected=set(load(ORDINARY/'SOURCE_PINS.json')['files'])|{str(p.relative_to(ROOT)) for p in ORDINARY.rglob('*') if p.is_file()}
    need(set(pins['files'])==expected,'complete exact source-only dependency inventory')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole literal dependency '+n)
    return load(PARENT/'source.json'),load(PARENT/'transform_certificate.json'),load(RAW)
def raw_expander(raw,old):
    retained={v['name']:i for i,v in enumerate(old['variables'])};memo={};pending=set()
    def token(t):
        if t[0]=='c':return C(t[1])
        need(t[0]=='v','raw semantic atom type');i=t[1]
        if i in memo:return memo[i]
        name=raw['variables'][i]['name']
        if name in retained:memo[i]=V(retained[name]);return memo[i]
        need(i not in pending and str(i) in raw['gates'],'complete raw affine gate restoration '+name);pending.add(i);row=raw['rows'][raw['gates'][str(i)]];p=P(row['terms']);co=p.pop((i,),0);need(co in [-1,1] and not any(i in m for m in p),'monic actual raw gate')
        result={}
        for mon,c in p.items():
            term=C(-c//co)
            for j in mon:term=times(term,token(['v',j]))
            result=plus(result,term)
        pending.remove(i);memo[i]=result;return result
    return token
def front_bindings(raw,old,cert):
    expand=raw_expander(raw,old);actual_calls=[dict(base=T(expand(p['base'])),exponent=T(expand(p['exponent'])),output=T(expand(p['output']))) for p in raw['powers']]
    need(actual_calls==cert['square_budget']['power_calls'] and len(actual_calls)==18,'complete original18 raw-to-affine power interfaces')
    atoms=[];seen=set()
    for p in raw['powers']:
        for key in ['base','exponent','output']:
            t=p[key];identifier=tuple(t)
            if identifier not in seen:seen.add(identifier);atoms.append(dict(token=t,affine=T(expand(t))))
    need(len(atoms)==37 and atoms==cert['square_budget']['atoms'],'all37actual semantic frame atoms')
    need(all(len(m)<=1 and all(j<245 for j in m) for atom in atoms for c,m in atom['affine']),'all semantic atoms affine and independent of the scale/cap/private witnesses')
    frame=total(V(245),C(-4),*[scale(square(P(atom['affine'])),-2) for atom in atoms]);need(frame==P(old['residuals'][445]['terms']),'complete even square-frame polynomial')
    expected_seeds=[]
    for prefix,x,y,target,ids in SEEDS:
        source=raw['seeds'][len(expected_seeds)];need(expand(source['pair'][0])==V(x) and expand(source['pair'][1])==V(y) and expand(source['exponent'])==P(target),'every original independent target/pair')
        need(ids==[i for i,p in enumerate(raw['powers']) if p['exponent']==source['exponent']],'all supporting calls for each pair');expected_seeds.append(dict(prefix='index'+str(prefix),pair=[x,y],target=T(P(target)),calls=ids))
    need(len(expected_seeds)==len(raw['seeds'])==15,'all original seeds accounted for')
    return expected_seeds,actual_calls,atoms
def expected_literal(old,cert,seeds):
    deleted=set(range(418,434))|{i for group in DELETE_GROUPS for i in group};variables=deepcopy(old['variables'])+[dict(name='index_cap.'+n,kind='signed_cap_witness') for n in CAP_NAMES]
    cap=[rr('index_cap.AY',total(V(524),scale(times(V(246),V(523)),-1))),rr('index_cap.norm',total(square(V(522)),square(V(523)),scale(square(V(524)),-1),C(-1))),rr('index_cap.Y2',total(V(525),scale(square(V(523)),-1))),rr('index_cap.BR',total(V(528),scale(V(527),-1),scale(times(V(255),V(527)),-1))),rr('index_cap.comparison_norm',total(square(V(526)),square(V(527)),scale(square(V(528)),-1),C(-1))),rr('index_cap.S_mod_U',total(V(526),scale(V(522),-1),scale(times(V(250),V(529)),-1))),rr('index_cap.R_mod_4Y',total(V(527),scale(V(245),-1),scale(times(V(523),V(530)),-4)))]
    lower=plus(V(523),V(245),-1);bound=total(square(V(523)),C(-1),*[scale(square(V(s['pair'][1])),-1) for s in seeds]);pool=total(*[square(plus(V(s['pair'][1]),P(s['target']),-1)) for s in seeds],square(plus(V(523),V(245),-1)),scale(times(V(246),V(531)),-1),V(531))
    cap += [rr('index_cap.lower_guard',graph(lower,532,533,534)),rr('index_cap.square_bound_guard',graph(bound,535,536,537)),rr('index_cap.joint_residue',pool)]
    rows=[];rowmap=[]
    for i,row in enumerate(old['residuals']):
        if i in deleted:rowmap.append(dict(old_row=i,status='deleted_private',new_row=None));continue
        new=deepcopy(row);status='retained'
        if i==434:new=rr('shared_index.V_positive_cap_square',total(V(251),scale(V(525),-1),scale(times(V(525),V(510)),-1)));status='new_cap_product'
        if i in LINEAR:
            m=LINEAR[i];p=P(row['terms']);need(p.get((m,m))==-1 and (m,) not in p,'entire old squared output term');new=rr(row['label'],total(p,square(V(m)),scale(V(m),-1)));status='restored_linear_output'
        rowmap.append(dict(old_row=i,status=status,new_row=len(rows)));rows.append(new)
        if i==209:rows+=cap
    retained=[(i,g) for i,g in enumerate(cert['guards']) if g.get('coordinate') not in {246,261,278}]
    used={j for r in rows for c,m in r['terms'] for j in m}|{j for _,g in retained for c,m in g['expression'] for j in m};mapping={j:i for i,j in enumerate(sorted(used))}
    body=dict(schema='signed_pell_joint_cap_body_v1',domain='unrestricted integers',variant='original_undoubled_targets_joint_signed_cap_source_only',variables=[variables[j] for j in sorted(used)],residuals=[rr(r['label'],move(P(r['terms']),mapping)) for r in rows],polynomial='sum of squares of all residuals',parent_source_sha256=PARENT_SHA,ordinary_manifest_sha256=SEAL)
    guarded=deepcopy(body);guards=[]
    for j,oldg in retained:
        g=deepcopy(oldg);g.pop('row');g.pop('auxiliary');g['expression']=T(move(P(g['expression']),mapping))
        if 'coordinate' in g:g['coordinate']=mapping[g['coordinate']]
        if 'pair' in g:g['pair']=[mapping[i] for i in g['pair']]
        a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3);guarded['variables'] += [dict(name=f'guard{j}.{s}',kind='integer_guard') for s in ['a','b','c']];g.update(original_guard_index=j,auxiliary=[a,b,c],row=len(guarded['residuals']));guarded['residuals'].append(rr('domain_guard.'+str(j),graph(P(g['expression']),a,b,c)));guards.append(g)
    for kind,p,aux,label in [('cap_lower',lower,[532,533,534],'index_cap.lower_guard'),('cap_square_bound',bound,[535,536,537],'index_cap.square_bound_guard')]:guards.append(dict(kind=kind,expression=T(move(p,mapping)),auxiliary=[mapping[j] for j in aux],row=next(i for i,r in enumerate(body['residuals']) if r['label']==label)))
    private=set(range(495,510))|{511}
    for prefix,x,y,target,ids in SEEDS:
        pre='index'+str(prefix)
        private|={i for i,v in enumerate(old['variables']) if v['name'] in {pre+'.'+s for s in ['S','R','YminusK','Squotient','Rquotient']}}
        for suffix in ['norm3','S_mod_U','R_mod_4Y']:
            r=next(r for r in old['residuals'] if r['label']==pre+'.'+suffix);candidates=[m[0] for c,m in r['terms'] if c==-1 and ((len(m)==2 and m[0]==m[1]) if suffix=='norm3' else len(m)==1) and old['variables'][m[0]]['kind']=='gate'];need(len(candidates)==1,'exact deleted comparison helper');private.add(candidates[0])
    need(not [(i,j) for i,r in enumerate(old['residuals']) if i not in deleted|{434} for j in private if any(j in m for c,m in r['terms'])],'whole private subgraph nonescape')
    need(not any(j in private for _,g in retained for c,m in g['expression'] for j in m),'whole retained-domain private nonescape')
    plan=dict(schema='source_only_signed_cap_literal_map_v1',old_source_sha256=PARENT_SHA,ordinary_manifest_sha256=SEAL,complete_old_row_map=rowmap,deleted_private_coordinates=sorted(private),omitted_scalar_guards=[246,261,278],raw_to_body=[[j,i] for j,i in mapping.items()],unused_raw_coordinates=sorted(set(range(len(variables)))-used),all_original_seeds=seeds,retained_guard_indices=[i for i,g in retained],cap_reserved_raw_slots={s:522+i for i,s in enumerate(CAP_NAMES)},frame_row_old=445,frame_variable_old=245,semantic_body_pointwise_preserved=False,semantic_front_rows_preserved=list(range(202)),witness_transfer='Reconstruct fresh complete Pell/cap/guard witnesses at the unchanged semantic front. No pointwise old full-body or old selected-Pell identity is claimed.',source_only=True,optimizer_executed=False,factorization_executed=False,projection_executed=False,accepted_frontier_claim=False)
    return {'source.json':body,'guarded.json':guarded,'domain.json':dict(schema='signed_cap_source_domain_graphs_v1',guards=guards),'TRANSFORM.json':plan},rows,rowmap,mapping,retained
def sign_replay(old,cert,rows,rowmap,retained):
    need(all(g['kind']!='nonnegative' or P(g['expression'])==V(g['coordinate']) for _,g in retained),'every literal scalar-guard expression matches its premise')
    scalars={g['coordinate'] for _,g in retained if g['kind']=='nonnegative'};need(3 in scalars and {7,8,185,247,252}<=scalars,'F retained; raw bootstrap/frame/comparison guards retained')
    need(P(old['residuals'][3]['terms'])==total(V(5),scale(V(7),-1),scale(V(8),-1),C(-1)) and P(old['residuals'][167]['terms'])==total(V(179),scale(V(5),-1),scale(V(185),-1),C(-1)),'raw B>=1 and q>=2 before powers')
    need(any(g['kind']=='positive_common_V' and P(g['expression'])==plus(V(251),C(1),-1) for _,g in retained),'strict common ordinate guarded independently of primary signs')
    known=set(scalars)|{5,179,245,251};pairs=[]
    for pair in cert['paired_guards']:
        u,s=pair['pair'];a,b=pair['anchor'];need({a,b}<=known,'direct retained weighted anchor')
        need(any(g['kind']=='paired_interval' and g['pair']==[u,s] and P(g['expression'])==times(V(u),V(s)) for _,g in retained),'whole paired guard expression')
        lhs=plus(P(old['residuals'][pair['anchor_row']]['terms']),P(old['residuals'][pair['row']]['terms']),-1);rhs=total(times(V(179),plus(V(u),V(a),-1)),V(s),scale(V(b),-1));need(lhs==rhs,'complete weighted common-bound identity');known|={u,s};pairs.append([u,s])
    eligible=[];skipped=[]
    for step in cert['sign_inference']['proof_steps']:
        entry=rowmap[step['row']]
        if entry['status']!='retained':skipped.append(step['row']);continue
        r=P(rows[entry['new_row']]['terms']);need(r==P(old['residuals'][step['row']]['terms']),'actual retained sign row');rhs=P(step['rhs']);c=step['coefficient'];need(c>0 and r in [plus(scale(V(step['variable']),c),rhs,-1),scale(plus(scale(V(step['variable']),c),rhs,-1),-1)],'complete sign-ledger polynomial identity')
        if step['kind']=='positive_monomials':
            need(all(co>0 for co in rhs.values()),'positive-coefficient sign constructor');deps={j for m in rhs for j,n in Counter(m).items() if n%2};need(deps==set(step['dependencies']),'exact odd-factor dependencies')
        else:need(step['kind']=='affine_square' and all(len(m)<=1 for m in P(step['square_root'])) and square(P(step['square_root']))==rhs and not step['dependencies'],'entire identified affine-square sign constructor')
        eligible.append(step)
    changed=True
    while changed:
        changed=False
        for step in eligible:
            if set(step['dependencies'])<=known and step['variable'] not in known:known.add(step['variable']);changed=True
    required=set(cert['sign_inference']['semantic_required'])-{246,261,278};need(required<=known,'entire retained early semantic sign closure without deleted rows/premises')
    return dict(verified_retained_sign_identities=len(eligible),skipped_changed_or_deleted_rows=skipped,required_targets=sorted(required),weighted_pairs=pairs,known_nonnegative=sorted(known),F_guard_retained=True,A_or_primary_ordinate_guard_assumed=False)
def semantic_cuts(old,rows,rowmap,seeds,calls):
    definitions={}
    for i,v in enumerate(old['variables']):
        if v['kind']!='gate' and v['name']!='index_addition.D':continue
        found=[]
        for r in old['residuals']:
            allowed=['index_addition.D_definition'] if v['name']=='index_addition.D' else ['addition','multiplication']
            if r['label'] not in allowed:continue
            p=P(r['terms']);co=p.get((i,),0)
            if (co==1 if v['kind']=='gate' else co in [-1,1]) and not any(i in m for m in p if m!=(i,)):found.append((co,p))
        if len(found)==1:definitions[i]=found[0]
    boundary=set(range(245))|{246,250,251,252,253,255,510}|{j for s in seeds for j in s['pair']}|{268,285,291,307,313}|{i for i,v in enumerate(old['variables']) if v['name'].startswith('pow') and v['name'].endswith('.quotient')}
    def expand(p,stop):
        memo={};pending=set()
        def symbol(i):
            if i in stop:return V(i)
            if i in memo:return memo[i]
            need(i in definitions and i not in pending,'complete acyclic local gate boundary '+str(i));pending.add(i);co,q=definitions[i];memo[i]=walk(scale(plus(q,scale(V(i),co),-1),-1//co));pending.remove(i);return memo[i]
        def walk(q):
            out={}
            for m,c in q.items():
                term=C(c)
                for j in m:term=times(term,symbol(j))
                out=plus(out,term)
            return out
        return walk(p)
    for seed in seeds:
        norm=next(r for r in old['residuals'] if r['label']==seed['prefix']+'.norm1');x,y=seed['pair'];want=total(square(V(x)),square(V(y)),scale(times(square(V(246)),square(V(y))),-1),C(-1));need(expand(P(norm['terms']),boundary)==want,'complete retained principal norm '+seed['prefix'])
    powercuts=[]
    for call,port in enumerate(calls):
        rowid=next(i for i,r in enumerate(old['residuals']) if r['label']==f'pow{call}.power_congruence');actual=P(rows[rowmap[rowid]['new_row']]['terms']);d=next(i for i,v in enumerate(old['variables']) if v['name']==f'pow{call}.quotient')
        if call==6:x=total(times(V(246),V(257)),times(plus(square(V(246)),C(1),-1),V(258)));y=total(V(257),times(V(246),V(258)))
        else:seed=next(s for s in seeds if call in s['calls']);x,y=map(V,seed['pair'])
        modulus={0:268,1:285,2:291,3:307,4:313,5:307,6:313,7:307,8:307,9:307,10:307,11:313,12:307,13:307,14:313,15:307,16:307,17:307}[call]
        want=total(x,times(plus(P(port['base']),V(246),-1),y),scale(P(port['output']),-1),scale(times(V(modulus),V(d)),-1));need(expand(actual,boundary)==want,'whole unsquared original power congruence '+str(call));powercuts.append(call)
    # Modulus coordinates are shared, and every one retains its exact definition.
    for target,rowid,base in [(268,221,calls[0]['base']),(285,236,calls[1]['base']),(291,241,calls[2]['base']),(307,256,calls[3]['base']),(313,262,calls[4]['base'])]:
        n=P(base);want=total(C(-1),scale(V(target),-1),scale(times(V(246),n),2),scale(square(n),-1));stop=boundary-{175};need(expand(P(old['residuals'][rowid]['terms']),stop)==want,'complete retained shared modulus definition')
    return dict(all15_principal_norms=True,all18_original_unsquared_power_congruences=powercuts,all5_shared_moduli_retained=True,derived_t_plus_one_pair='unchanged one-step recurrence from the t pair')
def early_bounds(old,seeds,calls,signs):
    known=set(signs['known_nonnegative']);need({0,1,2,3,4,25,171}<=known,'all affine target leaves are already nonnegative')
    # This actual contracted front identity gives v25>=18 independently of
    # every Pell sign, power interpretation, or factorial-correctness claim.
    need(P(old['residuals'][10]['terms'])==total(V(25),C(-18),*[scale(V(i),-1) for i in [0,1,2,3]]),'entire raw K lower-bound identity')
    bounds={i:0 for i in known};bounds[25]=18;index_bounds=[]
    for seed in seeds:
        p=P(seed['target']);need(all(c>0 and len(m)<=1 and all(j in bounds for j in m) for m,c in p.items()),'whole positive affine original target')
        lower=sum(c*(bounds[m[0]] if m else 1) for m,c in p.items());need(lower>=1,'strict original target bound before powers');index_bounds.append(dict(prefix=seed['prefix'],target=seed['target'],lower_bound=lower))
    # The first supporting call is q^t, not the possibly-base-one F call.
    need(P(calls[4]['base'])==V(179) and P(calls[4]['exponent'])==plus(C(16),V(0)) and P(calls[0]['base'])==plus(C(1),V(4)),'literal noncircular t support and F call')
    ceiling=total(P(old['residuals'][1]['terms']),P(old['residuals'][2]['terms']),scale(P(old['residuals'][3]['terms']),-1))
    need(ceiling==total(V(6),V(8),scale(times(V(3),V(5)),-1)),'whole early factorial-ceiling combination')
    return dict(all_original_index_bounds=index_bounds,t_lower_bound=16,W_lower_bound=4+2*16**2,primary_target_count=15,primary_count_at_most_W_minus_two=15<=4+2*16**2-2,first_support_call=4,F_call_only_after_same_pair_oriented=0,exact_factorial_ceiling_row_coefficients=[[1,1],[2,1],[3,-1]],later_reconstruction_order=[1,2,6,11,14,3,5,7,8,9,10,12,13,15,16,17])
def cap_interfaces():
    # Complete polynomial lowerings at the exact reserved-slot boundary.
    A,Ccap,Xc,Uc,Vc,S,R=map(V,[246,523,522,250,251,526,527]);Bc=plus(C(1),V(255))
    D=plus(square(A),C(1),-1)
    need(total(square(Xc),square(Ccap),scale(square(times(A,Ccap)),-1),C(-1))==total(square(Xc),scale(times(D,square(Ccap)),-1),C(-1)),'entire signed cap norm lowering')
    need(total(square(S),square(R),scale(square(times(Bc,R)),-1),C(-1))==total(square(S),scale(times(plus(square(Bc),C(1),-1),square(R)),-1),C(-1)),'entire cap comparison norm lowering')
    need(total(square(Uc),square(Vc),scale(square(times(A,Vc)),-1),C(-1))==total(square(Uc),scale(times(D,square(Vc)),-1),C(-1)),'entire retained signed common norm lowering')
    return dict(full_absolute_A_anchor_norms=True,cap_B_is_one_plus_raw255=True,common_V_positive_and_d_nonnegative_retained=True,C_squared_divides_common_V=True,pool_quotient_signed=True,cap_and_private_ports_excluded_from_frame=True)
def validate(artifacts,old,cert,raw):
    seeds,calls,atoms=front_bindings(raw,old,cert);expected,rows,rowmap,mapping,retained=expected_literal(old,cert,seeds)
    need(set(artifacts)==set(expected),'closed generated source-only output inventory')
    for n,data in expected.items():need(artifacts[n]==data,'whole generated literal artifact '+n)
    parent=artifacts['guarded.json'];used={i for r in parent['residuals'] for c,m in r['terms'] for i in m};need(used==set(range(len(parent['variables']))) and len({v['name'] for v in parent['variables']})==len(parent['variables']),'every raw guarded coordinate occurs; unique names')
    need(all(type(c) is int and len(m)<=2 and all(type(i) is int and 0<=i<len(parent['variables']) for i in m) for r in parent['residuals'] for c,m in r['terms']),'entire integer quadratic residual list')
    need(all(rowmap[i]['status']=='retained' for i in range(202)),'whole literal semantic front preserved')
    signs=sign_replay(old,cert,rows,rowmap,retained);bounds=early_bounds(old,seeds,calls,signs);cuts=semantic_cuts(old,rows,rowmap,seeds,calls)
    # The scale lowering is checked by complete substitution before any power.
    W,A,z=V(245),V(246),V(247);u=times(W,plus(z,C(1)));v=times(plus(W,C(1)),u);scale_norm=total(square(A),square(u),scale(square(v),-1),C(-1));want=total(square(A),scale(times(times(square(W),W),times(plus(W,C(2)),square(plus(z,C(1))))),-1),C(-1));need(scale_norm==want,'entire frame Pell norm lowering')
    return dict(all37_frame_ports=atoms,all_original_seeds=seeds,early_signs=signs,prepower_bounds=bounds,semantic_interfaces=cuts,absolute_cap_interfaces=cap_interfaces(),complete_cap_anchor_rows=True,direct_C_minus_W_guard=True,joint_cap_term_present=True,whole_source_only_artifacts=True,source_equivalence_or_frontier_accepted=False)
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--packet',type=Path,default=HERE);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();old,cert,raw=authenticate()
    files=['source.json','guarded.json','domain.json','TRANSFORM.json'];artifacts={n:load(args.packet/n) for n in files};evidence=validate(artifacts,old,cert,raw);rejected=[]
    controls=[('joint cap term','source.json','index_cap.joint_residue'),('cap lower guard','source.json','index_cap.lower_guard'),('cap squared range','source.json','index_cap.square_bound_guard'),('absolute-scale cap norm','source.json','index_cap.norm'),('cap comparison','source.json','index_cap.R_mod_4Y'),('front identity','source.json','choose0.digit_bound'),('linear original output','source.json','pow3.power_congruence'),('even frame','source.json','shared.frame_definition'),('common cap divisor','source.json','shared_index.V_positive_cap_square')]
    for label,name,target in controls:
        bad=deepcopy(artifacts);r=next(r for r in bad[name]['residuals'] if r['label']==target);r['terms'][0][0]+=1
        try:validate(bad,old,cert,raw)
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise ValueError('actual source corruption accepted '+label)
    for label,name,edit in [('missing old row map','TRANSFORM.json',lambda d:d['complete_old_row_map'].pop()),('hidden F guard deletion','domain.json',lambda d:d['guards'].pop(next(i for i,g in enumerate(d['guards']) if g.get('original_guard_index')==2))),('wrong signed domain','guarded.json',lambda d:d.update(domain='nonnegative integers'))]:
        bad=deepcopy(artifacts);edit(bad[name])
        try:validate(bad,old,cert,raw)
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise ValueError('actual whole artifact corruption accepted '+label)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_only=True,scope='Complete literal/guard/frame/semantic-interface checks at the approved ordinary cap theorem. No optimizer, factorization, projection, collected quartic or accepted frontier claim.',evidence=evidence,rejected_actual_artifacts=rejected,input_pins=load(HERE/'SOURCE_PINS.json'),generated_sha256={n:digest(args.packet/n) for n in files},checker_sha256=digest(Path(__file__)),builder_or_parent_or_incoming_program_executed=False)
    text=encode(result)
    if args.output.exists():need(args.output.read_bytes()==text,'refuse changed receipt overwrite')
    else:args.output.write_bytes(text)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_only=True,whole_artifacts=True,corruptions_rejected=len(rejected),no_optimizer_factorization_or_projection=True),sort_keys=True))
if __name__=='__main__':main()
