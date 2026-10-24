#!/usr/bin/env python3
"""Literal source cuts and small-ordinate/radius diagnostics for the76-guard proof.

No optimizer, emitter or source builder is imported. The unbounded argument
is PROOF.md; finite controls supplement its exact polynomial identities.
"""
import argparse
from hashlib import sha256
import importlib.util
import json
from math import comb
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def need(ok,message):
    if not ok:raise ValueError(message)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'entire source pin '+name)
    spec=importlib.util.spec_from_file_location('radius_guard_independent_sparse',ROOT/'reviews/main-root-modulus-signs-peer.py')
    p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
    P,C,V,add,mul=p.P,p.C,p.V,p.plus,p.times
    data=load(ROOT/'research/paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json')
    prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    old=load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    original={g['raw_variable']for g in old['guards']}
    removed={674,711,779,861,1214};kept=original-removed
    need(len(original)==78 and len(kept)==73 and 694 in kept,'exact76-guard scalar boundary')
    need(set(prior['prefix_proof']['initial_semantic_guard_indices'])<=kept,'all61 early sign premises retained without K/shiftedK slacks')
    need(pins['removed_original_predicates']==sorted(removed) and pins['new_predicates']==[
        dict(kind='at_least',raw_variable=656,lower=1),
        dict(kind='nonnegative_product',raw_variables=[674,861]),
        dict(kind='at_least',raw_variable=87,lower=2)],'strict V/product/factorial predicates')
    rows=[P(r['terms'])for r in raw['rows']];cut_count=0
    def ideal(cut,target=None):
        nonlocal cut_count
        out={}
        for term in cut['row_combination']:out=add(out,mul(P(term['multiplier']),rows[term['row']]))
        if target is None:target=P(cut.get('polynomial',cut.get('expanded_polynomial')))
        need(out==target,'every coefficient of literal source cut');cut_count+=1
        return out
    expected={
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
      'K_input':[[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]]}
    for name,target in expected.items():ideal(data['cuts'][name],P(target))
    ideal(data['M_constructor'],P([[1,[]],[1,[87]],[1,[87,59]],[-1,[129]]]))
    need({59,93,94,95,113,534,535,536,537}<=kept,'all actual digit and radix signs still explicit')
    for ci,n,k,m,x,y,si,slack in [(1,92,86,93,707,708,1,711),(6,530,86,533,707,708,1,711),(5,531,90,532,775,776,2,779)]:
        call=prior['power_calls'][ci];seed=prior['seeds'][si]
        need([raw['powers'][ci][name] for name in ['base','exponent','output']]==[['v',z]for z in [n,k,m]],'actual three call arguments')
        need([call['X'],call['Y']]==[x,y] and seed['aliases']['YminusK']==slack and slack not in kept,'exact unguarded seed pair')
        ideal(call['cut'],P([[1,[x]],[-1,[644,y]],[1,[n,y]],[-1,[m]],[-1,[call['modulus'],call['quotient']]]]))
        ideal(next(t['cut']for t in prior['moduli']if t['base']==n))
    for si,x,y,k,slack in [(1,707,708,86,711),(2,775,776,90,779)]:
        seed=prior['seeds'][si]
        for name,cut in seed['cuts'].items():ideal(cut)
        ideal(seed['cuts']['norm1'],P([[1,[x,x]],[-1,[644,644,y,y]],[1,[y,y]],[-1,[]]]))
        ideal(seed['cuts']['index_at_most_Y'],P([[1,[y]],[-1,[k]],[-1,[slack]]]))
    for name in ['frame_cut','bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence']:ideal(prior[name])
    ideal(data['whole_V_product'])
    # Universal four small-ordinate residue polynomials, before inequalities.
    A,n,m=V(0),V(1),V(2);T=add(mul(C(2),mul(A,n)),mul(n,n),-1);T=add(T,C(-1))
    expected_residues={(1,1):n,(-1,1):add(n,mul(C(2),A),-1),
                       (1,-1):add(mul(C(2),A),n,-1),(-1,-1):mul(C(-1),n)}
    for (sx,sy),want in expected_residues.items():
        out=add(mul(C(sx),A),mul(add(A,n,-1),C(sy)),-1)
        need(out==want,'universal smallY residue sign identity')
    bound=add(T,add(mul(C(2),A),add(n,m)),-1)
    rhs=add(mul(mul(C(2),A),add(n,C(-1))),add(mul(n,n),add(n,add(m,C(1)))),-1)
    need(bound==rhs,'complete modulus versus mixed-sign remainder margin')
    # Exact diagnostics cover the strict minimum modulus and all signed smallY.
    small=0
    for W in range(4,15):
        a=W**W+1
        for base in range(2,W):
            modulus=2*a*base-base*base-1
            for output in range(W):
                need(modulus>2*a+base+output and 2*a-base-output>0,'strict universal margins diagnostic')
                accepted=[]
                for sx,sy in [(1,1),(-1,1),(1,-1),(-1,-1)]:
                    if (sx*a-(a-base)*sy-output)%modulus==0:accepted.append((sx,sy))
                need(accepted==([(1,1)]if output==base else []),'exact smallY branch is positive exponent1 only');small+=1
    collapsed=0
    for K in range(3,8):
        for f in range(2,7):
            d=f*K*K;s=K+d;N=d+1;b=(f+1)*(N+1)
            need(b>s and 0<N<s,'collapsedK strict digit/radius bounds')
            output=(b+1)**s;q,u=divmod(output,b);digit=q%b
            need(u==1 and digit==s and (N+digit-1)//digit==1,'collapsedK gives f=1 from actual digit')
            for e in [1,K]:
                denom=b**e;quotient,remainder=divmod(b+1,denom);Cgot=quotient%b
                need((Cgot==1 and remainder==1)if e==1 else(Cgot==0),'collapsed shifted seed yields exact impossible digit')
            collapsed+=1
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_predicates=76,
        complete_original_row_identities=cut_count,actual_local_calls=[1,6,5],
        unchanged_prefix_premises=61,removed_original_predicates=sorted(removed),
        free_polynomial_smallY_identities=5,smallY_diagnostics=small,collapsed_digit_diagnostics=collapsed,
        source_pins={str((HERE/n).relative_to(ROOT)):digest(HERE/n)for n in ['PROOF.md','SOURCE_PINS.json','check.py']},
        scope='Ordinary76-predicate research proof with exact literal cuts and diagnostics. No projected metric, Lean or internal-ZFC theorem.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
