#!/usr/bin/env python3
"""Independent exact source audit for the 63-predicate signed-radius equation.

This file imports no producer, optimizer, previous checker, or proof compiler.
It authenticates the frozen source; proves all required finite polynomial
identities; audits the early sign dependency order; binds all109 private
completion constraints; and checks the literal new source/domain boundary.
The unbounded Pell, factorial, and logical arguments are in PROOF.md.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
SOURCE_HASHES={
 'domain75.json':'4038fe899bd0463556bf083ffe4bc78c6e051ae0627e059b4abdcc10b34ffb66',
 'first_output_sign_certificate.json':'d3cb63c408ae29c47eb848a29809319f660b0a54574a5693c81edef6810f06cf',
 'local_factorial_certificate.json':'2be4f7d49a5c473f71dae8227a791e415ee085d90d6db6f7b3bd31982d4de34a',
 'original_source_certificate.json':'96097a2984ab34468413c32898af70ee01c96d35470aaacc773654aca1140970',
 'parent75.json':'fd2efaad9da2c3e2b22aeb80a2924fb2e8ad6e922f357c140cd6a7fd23ad5eaf',
 'raw104_guard_certificate.json':'47463f6672fb0a154a114f02b2c5ba968125970c779789fa87ad7266a49d8437',
 'raw_builder.json':'2dc3a2acaeb95d09b22501ee4e978327c03c2cd50a1a0817eadda257651a0a75',
}
QUOTIENTS=[575,584,592,600,609,618,627,636]
OUTPUTS=[573,583,591,599,607,617,625,635,6,106]
REMOVED=QUOTIENTS+[104,6,106,825]

def need(b,s):
    if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def P(xs):
    d={}
    for c,m in xs:
        need(type(c)is int and isinstance(m,list)and all(type(v)is int and v>=0 for v in m),'literal integer terms')
        k=tuple(sorted(m));d[k]=d.get(k,0)+c
    return{m:c for m,c in d.items()if c}
def A(p,q,k=1):
    d=dict(p)
    for m,c in q.items():d[m]=d.get(m,0)+k*c
    return{m:c for m,c in d.items()if c}
def M(p,q):
    d={}
    for m,c in p.items():
        for n,b in q.items():
            k=tuple(sorted(m+n));d[k]=d.get(k,0)+b*c
    return{m:c for m,c in d.items()if c}
def V(v):return{(v,):1}
def C(c):return{():c}if c else{}
def neg(p):return{m:-c for m,c in p.items()}
def sq(p):return M(p,p)
def I(comb,rows):
    d={}
    for x in comb:
        need(type(x['row'])is int and 0<=x['row']<len(rows),'source row index')
        d=A(d,M(P(x['multiplier']),P(rows[x['row']]['terms'])))
    return d

def nonnegative(p,known,strict=False):
    z={}
    for mon,c in p.items():
        t=C(c)
        for v in mon:t=M(t,A(V(v),C(known.get(v,0))))
        z=A(z,t)
    return all(c>0 for c in z.values())and all(v in known or n%2==0 for m in z for v,n in Counter(m).items())and(not strict or z.get((),0)>0)

def collect_ideals(obj):
    found=[]
    if isinstance(obj,dict):
        if 'row_combination'in obj:found.append(obj['row_combination'])
        for v in obj.values():found+=collect_ideals(v)
    elif isinstance(obj,list):
        for v in obj:found+=collect_ideals(v)
    return found

def source_boundary(parent,domain,old,old_domain):
    need(parent['domain']=='unrestricted integers','unrestricted integer domain')
    need(parent['variables'][:1259]==old['variables'][:1259],'all1259 original coordinate identities')
    need(len(parent['variables'])==1259+3*63 and len(parent['residuals'])==1177+63,'complete63-predicate dimensions')
    need(domain['body_variables']==1259 and domain['body_rows']==1177,'original source dimensions')
    need(domain['removed_quotients']==QUOTIENTS and domain['signed_outputs']==OUTPUTS and domain['removed_guard_indices']==REMOVED,'exact changed domain record')
    change={}
    for m in OUTPUTS:change=A(change,A(V(m),sq(V(m)),-1))
    for i in range(1177):
        expected=P(old['residuals'][i]['terms'])
        if i==1176:expected=A(expected,change)
        label='shared.signed_output_frame_definition'if i==1176 else old['residuals'][i]['label']
        need(parent['residuals'][i]['label']==label and P(parent['residuals'][i]['terms'])==expected,'entire actual source body row '+str(i))
    guards=[g for g in old_domain['guards']if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables'][0]in REMOVED)]
    need(len(guards)==63 and len(domain['guards'])==63,'exact remaining63 predicates')
    for j,(source,g)in enumerate(zip(guards,domain['guards'])):
        need(g['predicate']==source['predicate'],'retained complete predicate '+str(j))
        a,b,c=range(1259+3*j,1262+3*j)
        need(g['auxiliary']==[a,b,c],'fresh disjoint guard coordinates')
        expected=P(g['predicate']['terms'])
        expected=A(expected,P([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
        need(P(parent['residuals'][1177+j]['terms'])==expected,'actual complete three-square row '+str(j))
    return{g['predicate']['raw_variables'][0]for g in guards if g['predicate']['kind']=='retained_scalar'}

def verify():
    src={}
    for name,h in SOURCE_HASHES.items():
        data=(HERE/'source'/name).read_bytes();need(sha256(data).hexdigest()==h,'whole frozen source '+name);src[name]=json.loads(data)
    old=src['parent75.json'];od=src['domain75.json'];raw=src['raw_builder.json'];cert=src['original_source_certificate.json']
    parent=load(HERE/'variants/63/parent.json');domain=load(HERE/'variants/63/domain.json')
    scalar=source_boundary(parent,domain,old,od);rows=raw['rows'];newrows=parent['residuals'][:1177]
    need(len(raw['variables'])==1259 and len(rows)==1177,'literal raw dimensions')
    need(old['variables'][:1259]==raw['variables'],'whole frozen variable metadata')
    need(old['residuals'][:1177]==[{k:v for k,v in r.items()if k in('label','terms')}for r in rows],'all original raw body rows')
    gates={}
    for i,r in enumerate(rows):
        g=r['gate']
        if g is None:continue
        p=P(r['terms']);need(p.get((g,))==1,'unit gate '+str(i))
        rhs={m:-c for m,c in p.items()if m!=(g,)}
        need(g not in gates and all(v<g for m in rhs for v in m),'unique triangular integer gate '+str(i));gates[g]=rhs
    need(len(gates)==1029,'all1029 source gates')
    known={v:0 for v in scalar if v<643};known[87]=2
    need({59,94,95,131}<=set(known),'early direct premises retained')
    # The first output sign is restored before any prefix inference.
    wanted=P([[1,[93]],[-1,[87,94]],[-1,[87,95]],[1,[95]],[-1,[87]]])
    need(any(I(c,rows)in(wanted,neg(wanted))for c in collect_ideals(src['first_output_sign_certificate.json'])),'complete original N=f*r+(f-1)s+f ideal')
    known[93]=2
    newbound=src['raw104_guard_certificate.json']
    strict104=P([[1,[87,104]],[1,[87]],[-1,[87,59]],[-1,[131]],[-3,[]]])
    need(I(newbound['row_combination'],rows)==strict104,'full11-row raw104 ideal')
    # f*(x+1)=f*z+s+3>0 and f>=2 imply integer x>=0.
    known[104]=0
    pfx=cert['prefix_proof']
    for b in pfx['preliminary_t_n_bounds']:
        F,G=P(b['factor']),P(b['rhs'])
        need(I(b['row_combination'],rows)==A(M(V(b['variable']),F),G,-1),'preliminary lower-bound ideal')
        need(nonnegative(F,known,True)and nonnegative(A(G,F,-(b['lower']-1)),known,True),'preliminary bound premises')
        known[b['variable']]=b['lower']
    skipped=[];used=[];postponed=[]
    for stage in pfx['five_stages']:
        for st in stage['preceding_sign_steps']:
            rhs=P(st['rhs']);target={(st['variable'],):st['coefficient']}
            need(type(st['coefficient'])is int and st['coefficient']>0,'positive sign pivot')
            need(P(rows[st['row']]['terms'])in(A(target,rhs,-1),neg(A(target,rhs,-1))),'whole sign-row identity')
            if st['kind']=='affine_square':
                need(sq(P(st['square_root']))==rhs,'complete affine square');valid=True
            else:
                need(st['kind']=='positive_monomials','known sign inference');valid=nonnegative(rhs,known)
            if valid:known.setdefault(st['variable'],0);used.append(st['row'])
            else:skipped.append(st['variable'])
        v=stage['variable'];F,G=P(stage['factor']),P(stage['rhs'])
        need(I(stage['row_combination'],rows)==A(M(V(v),F),G,-1),'whole special factor-bound identity')
        if nonnegative(F,known,True)and nonnegative(A(G,F,-(stage['lower']-1)),known,True):known[v]=max(known.get(v,0),stage['lower'])
        else:postponed.append(v)
    for st in pfx['final_sign_steps']:
        rhs=P(st['rhs']);need(P(rows[st['row']]['terms'])==A({(st['variable'],):st['coefficient']},rhs,-1),'last prefix row')
        need(nonnegative(rhs,known),'last prefix dependencies');known[st['variable']]=0
    missing=set(range(643))-set(known)
    expected_missing={6,106,124,125,130,132,133,573,575,579,580,583,584,587,588,591,592,595,596,599,600,603,604,607,609,613,614,617,618,621,622,625,627,631,632,635,636,639,640}
    need(missing==expected_missing and len(known)==604 and postponed==[130],'exact early604-sign boundary')
    args=set(cert['frame_arguments'])
    actual_args={p[k][1]for p in raw['powers']for k in('base','exponent','output')}
    need(args==actual_args and len(args)==43 and args-set(known)==set(OUTPUTS),'all43 frame atoms, precisely10 unsigned')
    expected=A(V(643),C(-2))
    for v in args-set(OUTPUTS):expected=A(expected,V(v),-1)
    for v in OUTPUTS:expected=A(expected,sq(V(v)),-1)
    need(I(cert['frame_cut']['row_combination'],newrows)==expected,'complete squared frame ideal')
    # Positive index constructors are literal row facts, unaffected by delayed outputs.
    exponents=[p['exponent'][1]for p in raw['seeds']]
    need(set(exponents)<=set(known),'all seed indices nonnegative before semantics')
    positive={4,5,129}
    for st in cert['positive_prefix']['steps']:
        v,r=st['variable'],st['row'];q=P(rows[r]['terms'])
        need(rows[r]['gate']==v and q.get((v,))==1,'positive constructor is an actual gate')
        rhs={m:-c for m,c in q.items()if m!=(v,)};w=tuple(sorted(st['positive_monomial']))
        need(w in rhs and all(c>0 for c in rhs.values()),'positive constructor coefficients')
        if v in known and set(w)<=positive:positive.add(v)
    need(set(exponents)<=positive,'all15 seed indices strictly positive in filtered proof')
    need({5,92,103,112,530,531}<=positive,'six constructor bases positive')
    # Every private completion equation is checked from its exact original rows.
    labels={r['label']:i for i,r in enumerate(rows)if r['gate']is None};covered={}
    def check(label,cut,target,changed=False):
        i=labels[label];need(i>=594,'private equation')
        rr=newrows if changed else rows
        need(I(cut['row_combination'],rr)==target,'whole private target '+label)
        ng=[x for x in cut['row_combination']if rows[x['row']]['gate']is None]
        need(len(ng)==1 and ng[0]['row']==i and P(ng[0]['multiplier'])in(C(1),C(-1)),'one private nongate with unit coefficient '+label)
        covered[i]=label
    norm=lambda a,x,y:A(A(sq(x),M(A(sq(a),C(-1)),sq(y)),-1),C(-1))
    W=V(643);D=A(sq(V(644)),C(-1))
    check('shared.last_norm',cert['bootstrap_norm'],A(A(sq(V(644)),M(M(M(sq(W),W),A(W,C(2))),sq(V(646))),-1),C(-1)))
    check('shared_index.norm',cert['unit_norm_cut'],norm(V(644),V(655),V(656)))
    check('shared_index.B_mod_U',cert['comparison_base_congruence'],A(A(V(667),V(644),-1),M(V(655),V(658)),-1))
    for s in cert['seeds']:
        al=s['aliases'];X,Y,S,R,k,h,sq0,rq=[V(al[n])for n in('X','Y','S','R','k','YminusK','Squotient','Rquotient')]
        pref=raw['variables'][al['X']]['name'].removesuffix('.X')
        ts={'index_at_most_Y':A(A(Y,k,-1),h,-1),'norm1':norm(V(644),X,Y),'norm3':norm(V(667),S,R),'S_mod_U':A(A(S,X,-1),M(V(655),sq0),-1),'R_mod_4Y':A(A(R,k,-1),M(M(C(4),Y),rq),-1)}
        for n,t in ts.items():check(pref+'.'+n,s['cuts'][n],t)
    for m in cert['moduli']:
        n,T=V(m['base']),V(m['modulus'])
        check(raw['variables'][m['modulus']]['name']+'_definition',m['cut'],A(A(A(M(M(C(2),V(644)),n),sq(n),-1),C(-1)),T,-1))
    for p in cert['power_calls']:
        target=A(A(A(A(V(p['X']),M(V(p['base']),V(p['Y']))),M(V(644),V(p['Y'])),-1),V(p['output']),-1),M(V(p['modulus']),V(p['quotient'])),-1)
        check('pow'+str(p['index'])+'.power_congruence',p['cut'],target)
    product=C(1)
    for s in cert['seeds']:product=M(product,sq(V(s['aliases']['Y'])))
    check('shared_index.V_positive_product',cert['positive_V_product'],A(V(656),M(product,A(V(1214),C(1))),-1))
    check('shared.frame_definition',cert['frame_cut'],expected,True)
    check('index_addition.D_definition',cert['initial_A_D_bounds'][1],A(V(917),D,-1))
    need(set(covered)=={i for i,r in enumerate(rows)if i>=594 and r['gate']is None}and len(covered)==109,'all109 private completion targets covered')
    # Complete gate expansion for local cuts, stopping only at specified ports/free inputs.
    def expand(v,stops,memo):
        if v in memo:return memo[v]
        if v not in gates or v in stops:return V(v)
        p={}
        for m,c in gates[v].items():
            q=C(c)
            for a in m:q=M(q,expand(a,stops,memo))
            p=A(p,q)
        memo[v]=p;return p
    def expand_poly(p,stops):
        z={};memo={}
        for m,c in p.items():
            q=C(c)
            for a in m:q=M(q,expand(a,stops,memo))
            z=A(z,q)
        return z
    need(expand(921,{644,917,670,671},{})==A(M(V(644),V(670)),M(V(917),V(671))),'whole derived t+1 abscissa')
    need(expand(922,{644,917,670,671},{})==A(V(670),M(V(644),V(671))),'whole derived t+1 ordinate')
    # All first-factorial identities are actual source ideals. Their free cuts
    # use none of the seven late-sign coordinates except K's square input6,
    # which appears only through already proved nonnegative square gates.
    loc=src['local_factorial_certificate.json']
    first_targets={
      'radius':[[1,[89]],[-1,[87,86,86]]],
      'shift':[[1,[90]],[-1,[86]],[-1,[89]]],
      'pow1_base':[[1,[92]],[-1,[89]],[-1,[]]],
      'radix':[[1,[530]],[-1,[129]],[-1,[129,93]],[-1,[129,113]]],
      'radix_plus_one':[[1,[531]],[-1,[530]],[-1,[]]],
      'digit':[[1,[532]],[-1,[533,91]],[-1,[533,530,534]],[-1,[535]]],
      'remainder_bound':[[1,[533]],[-1,[535]],[-1,[536]],[-1,[]]],
      'digit_bound':[[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]],
      'factorial_ceiling':[[1,[87,91]],[-1,[93]],[-1,[95]]],
      'factorial_remainder_bound':[[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]],
      'odd_base103':[[1,[103]],[-1,[]],[-1,[5,87]]],
      'opposite_index_parity':[[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]],
      'K_input':[[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]],
    }
    need(set(loc['cuts'])==set(first_targets),'complete first-factorial cut list')
    for name,cut in loc['cuts'].items():need(I(cut['row_combination'],rows)==P(first_targets[name]),'complete first-factorial/parity cut '+name)
    for name in('M_constructor','main_t_norm','t_slack','k122_slack','whole_V_product'):
        cut=loc[name];need(I(cut['row_combination'],rows)==P(cut['polynomial']),'full late dependency '+name)
    local_needed={4,5,86,87,89,90,91,92,93,94,95,104,110,111,112,113,114,115,122,123,129,131,530,531,532,533,534,535,536,537,546,547,548,549,550,551,560}
    need(local_needed<=set(known),'every local-first-factorial/paired/second-factorial semantic sign available early')
    desired={0:[5,4,6,670,671],1:[92,86,93,707,708],2:[103,4,104,670,671],3:[87,4,106,670,671],4:[112,4,113,670,671],5:[531,90,532,775,776],6:[530,86,533,707,708],7:[531,110,546,821,822],8:[530,4,547,670,671],9:[531,122,560,857,858]}
    for j,expect in desired.items():need([cert['power_calls'][j][k]for k in('base','exponent','output','X','Y')]==expect,'exact late source call '+str(j))
    need(825 not in scalar and all(s['aliases']['YminusK']in scalar for s in cert['seeds']if s['selected_power_call']in(10,12,13,14,15,17,18,20)),'only intended additional index guard removed')
    # The second-factorial small-index contradiction uses these actual rows.
    local_stops={4,107,109,110,111,112,113,114,115,530,531,546,547,548,549,550,551}
    checks={
      'factorial1.remainder_bound':A(A(A(V(111),V(114),-1),V(115),-1),C(-1)),
      'choose1.digit':A(A(V(546),M(V(547),A(V(111),M(V(530),V(548)))),-1),V(549),-1),
      'choose1.remainder_bound':A(A(A(V(547),V(549),-1),V(550),-1),C(-1)),
      'choose1.digit_bound':A(A(A(V(530),V(111),-1),V(551),-1),C(-1)),
    }
    for label,target in checks.items():need(expand_poly(P(rows[labels[label]]['terms']),local_stops)==target,'second-factorial exact row '+label)
    need(expand(109,{4,107},{})==M(V(107),sq(V(4))),'second factorial radius d=f1*t²')
    need(expand(110,{4,109},{})==A(V(4),V(109)),'second factorial shifted exponent')
    need(expand(112,{109},{})==A(V(109),C(1)),'second factorial positive base')
    cfac=expand_poly(P(rows[labels['factorial1.ceiling']]['terms']),local_stops)
    crem=checks['factorial1.remainder_bound']
    target=A(A(M(V(107),V(111)),V(113),-1),V(115),-1)
    need(A(neg(cfac),crem)==target,'complete second-factorial ceiling identity')
    # Range-quotient signs and delayed quotient130 restore from literal rows.
    ranges=raw['ranges'];need(len(ranges)==8,'all eight ranges')
    ports={129,530,531}|{p[k][1]for p in raw['powers']for k in('base','exponent','output')}
    for j,(_,_,_,label)in enumerate(ranges):
        q=QUOTIENTS[j];m=OUTPUTS[j];rem=q+1;slack=q+2
        e=[574,574,574,574,608,608,626,626][j]
        target=A(A(V(m),M(M(V(q),V(129)),V(e)),-1),V(rem),-1)
        need(expand_poly(P(rows[labels[label+'.quotient_multiple']]['terms']),ports)==target,'exact range quotient '+str(j))
        target2=A(A(A(V(e),V(rem),-1),V(slack),-1),C(-1))
        need(expand_poly(P(rows[labels[label+'.remainder_bound']]['terms']),ports)==target2,'exact range remainder '+str(j))
        need(rem in scalar and slack in scalar,'all range remainder signs retained')
    need(expand(124,{106,107},{})==M(V(106),V(107)),'late positive product124')
    need(expand(125,{123,124},{})==M(V(123),V(124)),'late positive product125')
    mp=expand_poly(P(rows[labels['moduli_product.division']]['terms']),{125,126,129,130})
    need(mp==A(A(V(125),V(129),-1),M(V(126),V(130)),-1),'q130 exact division')
    mb=expand_poly(P(rows[labels['moduli_product.remainder_bound']]['terms']),{126,129,131})
    need(mb==A(A(A(V(126),V(129),-1),V(131),-1),C(-1)),'q130 exact strict modulus bound')
    # The new radius admits every finite positive power specification.
    # These identities prove n²>=|n| over integers and n²>=n; Pell existence
    # at either prescribed radius is supplied by the ordinary unit theorem.
    controls=[]
    bad=deepcopy(parent);bad['residuals'][1176]['terms'].append([1,[573,573]])
    try:source_boundary(bad,domain,old,od)
    except ValueError:controls.append('missing signed-output square')
    else:raise ValueError('square corruption accepted')
    bad=deepcopy(parent);bad['residuals'][-1]['terms'].append([1,[87]])
    try:source_boundary(bad,domain,old,od)
    except ValueError:controls.append('changed final guard')
    else:raise ValueError('guard corruption accepted')
    bad=deepcopy(domain);bad['removed_guard_indices']=REMOVED+[131]
    try:source_boundary(parent,bad,old,od)
    except ValueError:controls.append('missing strict-modulus premise')
    else:raise ValueError('premise corruption accepted')
    return dict(status='PASS',python_optimized=not __debug__,source_hashes=SOURCE_HASHES,body_coordinates=1259,body_rows=1177,predicates=63,new_parent_integer_variables=len(parent['variables']),new_parent_rows=len(parent['residuals']),old_predicates=75,guard_triples_removed=12,signed_outputs=OUTPUTS,early_nonnegative_prefix=604,missing_early_prefix=sorted(missing),postponed_special_bound=130,whole_frame_arguments=43,private_nongates=len(covered),private_gate_definitions=sum(1 for i,r in enumerate(rows)if i>=594 and r['gate']is not None),all_gate_definitions=len(gates),late_call_schedule=dict(first_factorial=[1,5,6],paired_t=[2],paired_k122=[9],deferred_signed_outputs=[0,3],second_factorial=[4,7,8]),second_factorial_index_guard_removed=825,private_completion_coverage=covered,rejected_corruptions=controls,scope='Independent exact polynomial identities, actual source/predicate binding, sign dependency ledger and all109 private completion targets. Ordinary unbounded Pell/factorial/CRT and C222 calibration remain separate mathematical proofs; no new proof-assistant endpoint is asserted.')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',default='INDEPENDENT_SOURCE.json');args=ap.parse_args()
    result=verify();(HERE/args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('source_hashes','private_completion_coverage','missing_early_prefix')},indent=2))
if __name__=='__main__':main()
