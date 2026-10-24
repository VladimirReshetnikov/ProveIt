#!/usr/bin/env python3
"""Independent local original-row/digit/factorial audit; no emitter/optimizer.

Only the small collector from our earlier independent peer is imported.
Unbounded correctness is in LOCAL_FACTORIAL.md, not inferred from sampling.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from math import comb,factorial
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('independent_poly',ROOT/'reviews/main-root-modulus-signs-peer.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
P,C,V,add,mul,product=p.P,p.C,p.V,p.plus,p.times,p.product
def need(ok,message):
    if not ok:raise ValueError(message)
def load(path):return json.loads(path.read_bytes())
def sha(path):return sha256(path.read_bytes()).hexdigest()
def pell(a,k):
    x,y=1,0
    for _ in range(k):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y
def boolean(q,assignment={}):
    out={}
    for m,c in q.items():
        if any(assignment.get(v)==0 for v in m):continue
        key=tuple(sorted({v for v in m if assignment.get(v)!=1}))
        out[key]=(out.get(key,0)+c)%2
    return{m:c for m,c in out.items()if c}

def verify(data,raw,old,prior):
    rows=[P(row['terms'])for row in raw['rows']];oldguards={g['raw_variable']for g in old['guards']}
    need(data['removed_scalar_guards']==[674,861,1214]and data['retained_scalar_guards']==sorted(oldguards-{674,861,1214}),'exact old/private guard boundary')
    kept=set(data['retained_scalar_guards'])
    need(len(oldguards)==78 and len(kept)==75 and 694 in kept and {711,779}<=kept,'keep T0 and exactly the two local seed bounds')
    need(data['new_predicates']==[dict(kind='value_at_least',raw_variable=656,lower=1),dict(kind='nonnegative_product',raw_variables=[674,861])],'strictV and actual two-slack product, not weakV')
    prefix=prior['prefix_proof'];known={v:0 for v in prefix['initial_semantic_guard_indices']}
    need(len(known)==61 and set(known)<=kept,'all61 unchanged semantic premises')
    count=0
    def ideal(obj,target=None,prefix_only=False):
        nonlocal count
        q={}
        for term in obj['row_combination']:
            m=P(term['multiplier']);row=rows[term['row']]
            if prefix_only:need(p.vars_(m)|p.vars_(row)<=set(range(643)),'no private index/power meaning in prefix proof')
            q=add(q,mul(m,row))
        if target is None:target=P(obj.get('polynomial',obj.get('expanded_polynomial')))
        need(q==target,'every coefficient of complete original-row ideal');count+=1
        return q
    def strict(q):
        need(p.vars_(q)<=set(known),'only earlier prefix lower bounds used')
        out={}
        for m,c in q.items():out=add(out,product([C(c)]+[add(V(v),C(known[v]))for v in m]))
        need(all(c>=0 for c in out.values())and out.get((),0)>0,'universal strict polynomial lower bound')
    def bound(obj):
        v,L,F,G=obj['variable'],obj['lower'],P(obj['factor']),P(obj['rhs'])
        need(v not in p.vars_(F)|p.vars_(G),'no self sign premise');ideal(obj,add(mul(V(v),F),G,-1),True)
        strict(F);strict(add(G,mul(C(L-1),F),-1));known[v]=max(known.get(v,L),L)
    signcount=0
    def sign(step):
        nonlocal signcount
        v,c,R=step['variable'],step['coefficient'],P(step['rhs']);target=add(mul(C(c),V(v)),R,-1)
        need(v<643 and c>0 and p.vars_(rows[step['row']])<=set(range(643))and rows[step['row']]in[target,mul(C(-1),target)],'whole prefix sign row')
        if step['kind']=='positive_monomials':
            deps={v for m in R for v,n in Counter(m).items()if n%2};need(all(c>0 for c in R.values())and deps==set(step['dependencies'])and deps<=set(known),'prefix signs precede every odd power')
        else:need(step['kind']=='affine_square'and mul(P(step['square_root']),P(step['square_root']))==R,'complete square sign row')
        known[v]=max(known.get(v,0),0);signcount+=1
    for obj in prefix['preliminary_t_n_bounds']:bound(obj)
    for obj in prefix['five_stages']:
        for step in obj['preceding_sign_steps']:sign(step)
        bound(obj)
    for step in prefix['final_sign_steps']:sign(step)
    need(set(known)==set(range(643))and known[4]>=1 and known[5]>=2,'all643 prefix signs under reduced private hypotheses')
    expected={
      'radius':P([[1,[89]],[-1,[87,86,86]]]),
      'shift':P([[1,[90]],[-1,[86]],[-1,[89]]]),
      'pow1_base':P([[1,[92]],[-1,[89]],[-1,[]]]),
      'radix':P([[1,[530]],[-1,[129]],[-1,[129,93]],[-1,[129,113]]]),
      'radix_plus_one':P([[1,[531]],[-1,[530]],[-1,[]]]),
      'digit':P([[1,[532]],[-1,[533,91]],[-1,[533,530,534]],[-1,[535]]]),
      'remainder_bound':P([[1,[533]],[-1,[535]],[-1,[536]],[-1,[]]]),
      'digit_bound':P([[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]]),
      'factorial_ceiling':P([[1,[87,91]],[-1,[93]],[-1,[95]]]),
      'factorial_remainder_bound':P([[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]]),
      'odd_base103':P([[1,[103]],[-1,[]],[-1,[5,87]]]),
      'opposite_index_parity':P([[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]]),
      'K_input':P([[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]])}
    need(set(data['cuts'])==set(expected),'all digit/remainder/ceiling source cuts, none omitted')
    for name,target in expected.items():ideal(data['cuts'][name],target)
    ideal(data['M_constructor'],P([[1,[]],[1,[87]],[1,[87,59]],[-1,[129]]]))
    Ys=[s['pair'][1][1]for s in raw['seeds']]
    ideal(data['whole_V_product'],add(V(656),product([add(V(1214),C(1))]+[mul(V(y),V(y))for y in Ys]),-1))
    need({94,95,113,59,534,535,536,537}<=kept,'all actual extraction/radix slacks and unusedoutput113 signs retained')
    gates={row['gate']:P(row['terms'])for row in raw['rows']if row.get('gate')is not None}
    need(data['K_square_chain']==list(range(64,87)),'exact23-square constructor')
    for v in data['K_square_chain']:need(gates[v]==add(V(v),mul(V(v-1),V(v-1)),-1),'all literal K square rows')
    need(data['local_interpreted_calls']==[1,5,6]and data['parity_only_call']==2 and data['conditional_even_orientation_calls']==[0,9],'no premature missing-index power interpretation')
    tuples=[(1,92,86,93,707,708),(5,531,90,532,775,776),(6,530,86,533,707,708)]
    need(len(data['actual_calls'])==len(tuples),'exactly three interpreted local calls')
    for call,(i,n,k,m,x,y)in zip(data['actual_calls'],tuples):
        need(call==prior['power_calls'][i]and[n,k,m]==[raw['powers'][i][z][1]for z in('base','exponent','output')],'entire actual local power call and index binding')
        need((call['X'],call['Y'])==(x,y),'correct kept seed pair')
        target=P([[1,[x]],[-1,[644,y]],[1,[n,y]],[-1,[m]],[-1,[call['modulus'],call['quotient']]]]);ideal(call['cut'],target)
        mod=next(obj for obj in prior['moduli']if obj['base']==n);ideal(mod['cut'])
    for i in(1,2):
        seed=prior['seeds'][i];need(seed['aliases']['YminusK']in kept,'local short interval from retained guard')
        for cut in seed['cuts'].values():ideal(cut)
    need(len(data['conditional_calls'])==2 and len(data['missing_seeds'])==2,'exact two later even-index interfaces')
    for call,seed,ci,si,slack in zip(data['conditional_calls'],data['missing_seeds'],[0,9],[0,4],[674,861]):
        need(call==prior['power_calls'][ci] and seed==prior['seeds'][si],'entire actual conditional even-index call and seed')
        need(seed['aliases']['YminusK']==slack and [call['X'],call['Y']]==[seed['aliases']['X'],seed['aliases']['Y']],'conditional call uses its own missing bound')
        need([call[z] for z in ['base','exponent','output']]==[raw['powers'][ci][z][1] for z in ['base','exponent','output']],'conditional call raw constructor binding')
        for cut in seed['cuts'].values():ideal(cut)
        ideal(call['cut']);ideal(next(obj['cut'] for obj in prior['moduli'] if obj['base']==call['base']))
    ideal(prior['frame_cut']);ideal(prior['bootstrap_norm']);ideal(prior['unit_norm_cut']);ideal(prior['comparison_base_constructor']);ideal(prior['comparison_base_congruence'])
    need(data['parity_call']==prior['power_calls'][2]and data['parity_call']['X']==670 and data['parity_call']['Y']==671,'parity-only residue is at the unknown t pair')
    parity_call=ideal(data['parity_call']['cut']);tnorm=ideal(data['main_t_norm'],P([[1,[670,670]],[-1,[644,644,671,671]],[1,[671,671]],[-1,[]]]))
    need(boolean(add(parity_call,tnorm),{103:1,742:0})=={():1,(104,):1},'odd raw104 follows from norm+evenmodulus, no power meaning')
    need(boolean(expected['odd_base103'],{87:0})=={():1,(103,):1},'even factorial makes actual base103 odd')
    mod=next(obj for obj in prior['moduli']if obj['base']==103)
    need(boolean(P(mod['cut']['polynomial']),{103:1})=={(742,):1},'actual modulus742 is even')
    need(boolean(expected['opposite_index_parity'],{104:1})=={():1,(4,):1,(122,):1},'two actual indices have opposite parity')
    ideal(data['t_slack'],P([[1,[671]],[-1,[4]],[-1,[674]]]))
    ideal(data['k122_slack'],P([[1,[858]],[-1,[122]],[-1,[861]]]))
    return {'prefix_sign_rows':signcount,'prefix_coordinates':len(known),'complete_original_row_ideals':count,
            'local_interpreted_calls':[1,5,6],'exact_digit_extraction_cuts':3,'boolean_parity_identities':4}

def controls():
    digits=0
    for K in range(2,8):
        for f in range(1,10):
            d=f*K*K;N=(d+1)**K;n=K+d;C0=comb(n,K)
            for b in(N+1,2*N+1):
                need(all(comb(n,j)<=C0<=N<b for j in range(K+1)),'all low coefficients fit the actual strict radix bound')
                power=(b+1)**n;den=b**K;q,rem=divmod(power,den);Cgot=q%b
                need(Cgot==C0 and 0<=rem<den and power==den*(Cgot+b*(q//b))+rem,'full digit/remainder identities');digits+=1
    fixed=0
    for K in range(2,8):
        m=factorial(K)
        for f in range(1,m+3):
            d=f*K*K;N=(d+1)**K;C0=comb(K+d,K);ratio=Fraction(N,C0)
            need(Fraction(m*(2*f-1),2*f)<ratio<=m,'strict factorial product interval')
            need(((N+C0-1)//C0==f)==(f==m),'unique factorial ceiling fixed point');fixed+=1
    signs=0
    for W in range(3,8):
        A=W**W+1
        for k in range(2,W,2):
            x,y=pell(A,k)
            for n in range(2,W):
                T=2*A*n-n*n-1
                for m in range(W):
                    for sx,sy in[(-1,1),(1,-1),(-1,-1)]:
                        need((sx*x-(A-n)*sy*y-m)%T!=0,'all unwanted even-index coordinate signs excluded');signs+=1
    return dict(low_digit_cases=digits,factorial_fixedpoint_cases=fixed,unwanted_even_index_sign_cases=signs)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    data=load(HERE/'LOCAL_FACTORIAL_CERTIFICATE.json')
    for relative,h in data['source_pins'].items():need(sha(ROOT/relative)==h,'entire frozen source '+relative)
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    old=load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    result=verify(data,raw,old,prior);rejected=[]
    def reject(label,fn):
        try:fn()
        except(ValueError,KeyError,TypeError,IndexError):rejected.append(label)
        else:raise ValueError('corruption accepted '+label)
    bad=deepcopy(data);del bad['cuts']['digit_bound'];reject('omit actual digit bound',lambda:verify(bad,raw,old,prior))
    bad=deepcopy(data);bad['cuts']['remainder_bound']['row_combination'][0]['multiplier'][0][0]+=1;reject('change full remainder ideal',lambda:verify(bad,raw,old,prior))
    bad=deepcopy(data);bad['local_interpreted_calls'].append(2);reject('interpret missing t index before recovery',lambda:verify(bad,raw,old,prior))
    bad=deepcopy(data);bad['new_predicates'][0]['lower']=0;reject('weaken V positivity and permit zero ordinates',lambda:verify(bad,raw,old,prior))
    bad=deepcopy(data);bad['actual_calls'][2]['X']=775;reject('use wrong retained seed for radix denominator',lambda:verify(bad,raw,old,prior))
    result.update(status='PASS',optimized_python=bool(sys.flags.optimize),finite_controls=controls(),rejected_corruptions=rejected,
      source_pins={str(f.relative_to(ROOT)):sha(f)for f in[HERE/'README.md',HERE/'LOCAL_FACTORIAL.md',HERE/'LOCAL_FACTORIAL_CERTIFICATE.json',Path(__file__)]},
      scope='Complete local source/sign/digit/ceiling binding and ordinary research proof. Finite controls are diagnostics, no full21-power semantics, projected metric, Lean or internal-ZFC theorem.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
