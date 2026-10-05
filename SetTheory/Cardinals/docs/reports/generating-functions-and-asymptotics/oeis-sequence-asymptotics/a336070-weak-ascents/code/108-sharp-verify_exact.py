#!/usr/bin/env python3
"""Standalone report108 exact finite verifier. All mathematical arithmetic is int/Fraction.

q=-M log(r) is symbolic: H/q, b/q, c/q are rational. At r=1 these
are continuous normalized limits, while actual H,b,c are separately zero.
For capped rows s=exp(-p) and v=exp(q) are rational parameters; p,q
are not claimed rational. Finite checks do not prove any analytic estimate.
No assert statement is a correctness gate; python -O preserves every guard.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import sys
import weak_verify_exact as weak
from weak_verify_exact import require,equal,keys,integer,rational,vector,load_json
HERE=Path(__file__).resolve().parent
MS=(1,2,3,5,8,16)
RS=('1/5','1/2','2/3','9/10','99/100','1')
DS=(1,2,3,5,9,17)
CS=('1/5','1/2','9/10')
VS=('1','2','17','1024')
CDS=(0,1,2,3,4,5,6,9,17)
PDS=(1,2,3,5,9)
CN,PN=16,8
MODES=('stays_capped','time_only','increment_only','combined','q0_successor')
CURRENT_PHASE='preflight'
COUNTS=Counter()

def check(label,test,context=''):
    require(test,label+('; '+context if context else ''))
    COUNTS[label]+=1

def seq(value,length,context):
    require(type(value) is list,context+': expected list')
    equal(len(value),length,context+': complete inventory')
    return value

def naturals(value,length,context):
    seq(value,length,context)
    for x in value: require(integer(x,context)>=0,context+': negative count')
    return value

def schema(data):
    keys(data,('schema','scope','inventory','shifted_cases','capped_cases','crossing_cases','recurrences','prefix_cases'),'fixtures')
    equal(data['schema'],'report108-sharpened-exact-v1','schema')
    equal(data['scope'],'Finite integer/rational checks only; no analytic or uniform asymptotic estimate is certified.','scope')
    inv={'M':list(MS),'r':list(RS),'shift_d':list(DS),'cap_s':list(CS),'cap_v':list(VS),'cross_M':[2,3,5],'cross_t':['1/2','9/10'],'cross_modes':list(MODES),'count_d':list(CDS),'count_max_n':CN,'prefix_d':list(PDS),'prefix_max_n':PN}
    keys(data['inventory'],inv,'inventory'); equal(data['inventory'],inv,'fixed complete inventory')
    for key in ('M','shift_d','cross_M','count_d','prefix_d'):
        for val in data['inventory'][key]: integer(val,'inventory '+key)
    integer(data['inventory']['count_max_n'],'count_max_n'); integer(data['inventory']['prefix_max_n'],'prefix_max_n')
    for name,length in (('shifted_cases',len(MS)*len(RS)*len(DS)),('capped_cases',len(MS)*len(DS)*len(CS)*len(VS)),('crossing_cases',3*2*len(MODES)),('recurrences',len(CDS)),('prefix_cases',len(PDS)*PN)):
        seq(data[name],length,name)

def shifted_checks(cases,base):
    lookup={(c['M'],c['r']):c for c in base['frozen_cases']}
    for case,(M,rt,d) in zip(cases,product(MS,RS,DS)):
        keys(case,('M','r','d','rows'),'shifted case')
        equal((integer(case['M'],'M'),case['r'],integer(case['d'],'d')),(M,rt,d),'ordered shifted case inventory')
        r=F(rt); h=d-1; bcase=lookup[M,rt]
        v,lam=F(bcase['v']),F(bcase['lambda']); hc=list(map(F,bcase['h_scaled'])); c=F(bcase['c_scaled']); p=list(map(F,bcase['p']))
        for l,row in enumerate(seq(case['rows'],M,'shifted rows')):
            keys(row,('l','l_prime','m','normalizer','P','poisson_scaled','tracker_drift'),'shifted row')
            equal(integer(row['l'],'l'),l,'ordered row inventory')
            lp=integer(row['l_prime'],'l_prime'); m=integer(row['m'],'m')
            check('shift_clipped_index',lp==max(l-(d-1),0) and m==min(d-1,l) and lp+m==l)
            norm=rational(row['normalizer'],'normalizer'); prob=vector(row['P'],M,'shifted P')
            check('shifted_normalizer_formula',norm==lam*r**(-m))
            direct=sum((v if j>l-d else 1)*r**j for j in range(M))
            check('shifted_row_normalization',direct==norm*r**l)
            check('shifted_positive_stochastic',all(x>0 for x in prob) and sum(prob)==1)
            for j in range(M):
                a=int(j>l-d)
                check('threshold_convention',a==int(j>=lp))
                check('shifted_weak_row_identity',prob[j]==p[(j-lp)%M])
                check('shifted_doob_entries',prob[j]==(v if a else 1)*r**j/(norm*r**l))
                inc=F(a)+F(l,M)-F(j,M+a)
                rhs=1-F((j-lp)%M,M)+F(a*j,M*(M+a))+F(m,M)
                check('shifted_tracker_identity',inc==rhs)
                check('shifted_tracker_bounds',0<=inc<=2)
            actual=sum(prob[j]*(int(j>l-d)*F(j,M)+hc[j]-hc[l]) for j in range(M))
            target=c+hc[lp]-hc[l]
            check('shifted_poisson_cancellation',actual==target)
            check('shifted_poisson_fixture',rational(row['poisson_scaled'],'poisson_scaled')==target)
            drift=sum(prob[j]*(F(int(j>l-d))+F(l,M)-F(j,M+int(j>l-d))) for j in range(M))
            check('shifted_tracker_drift_fixture',rational(row['tracker_drift'],'tracker_drift')==drift)
            check('shifted_tracker_minimum_drift',drift>=F(1,2))
            if r==1:
                check('q0_shifted_uniform',norm==M and prob==[F(1,M)]*M)
                actual_h=[F(0)]*M; actual_b=actual_c=F(0)
                actual=sum(prob[j]*(0*int(j>l-d)*F(j,M)+actual_h[j]-actual_h[l]) for j in range(M))
                check('q0_shifted_actual_zero',actual==actual_c+actual_h[lp]-actual_h[l]==actual_b==0)
        if d>M: COUNTS['shift_cases_d_greater_than_M']+=1
        COUNTS['shifted_cases']+=1

def capped_checks(cases):
    for case,(M,d,st,vt) in zip(cases,product(MS,DS,CS,VS)):
        keys(case,('M','d','s','v','row_sums','bound'),'capped case')
        equal((integer(case['M'],'M'),integer(case['d'],'d'),case['s'],case['v']),(M,d,st,vt),'ordered capped inventory')
        s=rational(case['s'],'s'); v=rational(case['v'],'v'); h=d-1
        rows=vector(case['row_sums'],M,'cap rows'); bound=rational(case['bound'],'cap bound')
        check('cap_parameter_domain',0<s<1 and v>=1)
        check('cap_bound_formula',bound==(s**(-M)+v*s**(-h))/(1-s))
        for l in range(M):
            lp=max(l-h,0)
            direct=sum((v if j>l-d else 1)*s**(j-l) for j in range(M))
            check('cap_finite_row_sum',rows[l]==direct)
            check('cap_shifted_geometric_bound',direct<=bound)
            check('cap_clipped_geometric_formula',direct==s**(-l)*((1-s**lp)+v*(s**lp-s**M))/(1-s))
            for w in map(F,('1/10','1/2','1','3/2','7')):
                weighted=sum((v if j>l-d else 1)*(w if j==l else 1)*s**(j-l) for j in range(M))
                check('cap_positive_weight_domination',weighted<=max(F(1),w)*direct<=max(F(1),w)*bound)
        COUNTS['capped_cases']+=1

def crossing_checks(cases):
    for case,(M,tt,mode) in zip(cases,product((2,3,5),('1/2','9/10'),MODES)):
        keys(case,('M','t','mode','p_exponent','old_q_exponent','new_q_exponent','slope_drop_exponents','crossing_bound_exponent'),'crossing case')
        equal((integer(case['M'],'M'),case['t'],case['mode']),(M,tt,mode),'ordered crossing inventory')
        t=rational(case['t'],'t'); P=integer(case['p_exponent'],'p_exponent'); L=integer(case['old_q_exponent'],'old_q_exponent'); N=integer(case['new_q_exponent'],'new_q_exponent'); bound=integer(case['crossing_bound_exponent'],'crossing_bound_exponent')
        # q_old=-L log(t), q_new=-N log(t), p=-P log(t), 0<t<1.
        check('crossing_exponent_domain',0<t<1 and P==2*M*(M+1) and L>=N>=0 and L>P*M)
        expected_N={'stays_capped':P*(M+2),'time_only':P*(M-1),'increment_only':P*M+P//2,'combined':P*M,'q0_successor':0}[mode]
        expected_L=expected_N if mode=='increment_only' else max(expected_N,P*M)+P
        check('crossing_fixture_regime',N==expected_N and L==expected_L)
        check('crossing_bound_exponent',bound==P+L-N)
        seq(case['slope_drop_exponents'],2,'crossing rows')
        for a in (0,1):
            stored=vector(case['slope_drop_exponents'][a],M,'slope exponents')
            slope=min(F(N,M+a),F(P))
            for j in range(M):
                exponent=(P-slope)*j
                check('crossing_slope_drop_fixture',stored[j]==exponent)
                check('crossing_pointwise_exponent_bound',0<=exponent<=P+L-N)
                # Chosen exponent inventory is integral, so the exponential form is exact rational too.
                check('crossing_integral_exponent',exponent.denominator==1)
                ratio=t**(-int(exponent))
                check('crossing_exact_rational_bound',ratio<=t**(-bound))
            if N==P*(M+a): check('cap_equality_is_uncapped',slope==P and all(x==0 for x in stored))
            if N==0: check('q0_next_slope',slope==0)
        # Once uncapped, q decreases and M increases, so no return to a capped state.
        for old_uncapped in range(P*M+1):
            for a in (0,1):
                new_uncapped=max(0,old_uncapped-P)
                check('uncapped_successor_monotonicity',F(new_uncapped,M+a)<=F(old_uncapped,M)<=P)
        K=M-2
        check('cap_temporal_factor_favorable',t**((L-N)*K)<=1)
        s=t**P; v=t**(-N)
        for d in DS:
            for l in range(M):
                actual=F(0)
                for j in range(M):
                    a=int(j>l-d); slope=min(F(N,M+a),F(P))
                    exponent=(L-N)*K-N*a+slope*j-P*l
                    check('cap_full_transition_integral',exponent.denominator==1)
                    term=t**int(exponent)
                    frozen=(v if a else 1)*s**(j-l)
                    check('cap_full_transition_factorization',term==t**((L-N)*K)*frozen*t**int((slope-P)*j))
                    actual+=term
                frozen_bound=(s**(-M)+v*s**(-(d-1)))/(1-s)
                check('cap_full_successor_row_bound',actual<=t**(-bound)*frozen_bound)
        COUNTS['crossing_cases']+=1

def incoming_counts(d):
    layer={(0,0):1}; totals=[1,1]
    for n in range(2,CN+1):
        nxt={}
        for K in range(n):
            for j in range(K+1):
                nonasc=sum(layer.get((K,L),0) for L in range(j+d,K+1))
                asc=sum(layer.get((K-1,L),0) for L in range(min(K,j+d)))
                if nonasc+asc: nxt[K,j]=nonasc+asc
        layer=nxt; totals.append(sum(layer.values()))
    return totals

def enumerate_prefix(d,k):
    all_by=[0]*k; legal_by=[0]*k; seen=set()
    for x in product(*(range(i) for i in range(1,k+1))):
        # Independently compute ascents from transformed strict descents.
        y=tuple(x[i]+(d-1)*(i+1) for i in range(k))
        check('prefix_alphabet',all(0<=v<d*k for v in y))
        desc=[i for i in range(k-1) if y[i+1]<y[i]]
        r=len(desc)
        check('prefix_threshold_transform',all((y[i+1]>=y[i])==(x[i+1]>x[i]-d) for i in range(k-1)))
        all_by[r]+=1
        legal=all(x[i]<=1+(i-1)-sum(x[t+1]<=x[t]-d for t in range(i-1)) for i in range(1,k))
        if legal: legal_by[r]+=1
        endpoints=[0]+[i+1 for i in desc]+[k]
        blocks=[y[endpoints[b]:endpoints[b+1]] for b in range(r+1)]
        check('prefix_nondecreasing_runs',all(all(b[i]<=b[i+1] for i in range(len(b)-1)) for b in blocks))
        # Sparse multiplicities are equivalent to the D(r+1) stars-and-bars variables.
        encoding=tuple(tuple(sorted(Counter(block).items())) for block in blocks)
        check('prefix_injective_block_encoding',encoding not in seen)
        seen.add(encoding)
        decoded=tuple(v for block in encoding for v,count in block for _ in range(count))
        check('prefix_inverse_transform',tuple(decoded[i]-(d-1)*(i+1) for i in range(k))==x)
    return all_by,legal_by

def prefix_checks(cases,recurrences):
    by_d={row['d']:row['counts'] for row in recurrences}
    for case,(d,k) in zip(cases,product(PDS,range(1,PN+1))):
        keys(case,('d','k','inversion_words_by_r','legal_words_by_r','stars_bars'),'prefix case')
        equal((integer(case['d'],'d'),integer(case['k'],'k')),(d,k),'ordered prefix inventory')
        a=naturals(case['inversion_words_by_r'],k,'inversion histogram'); legal=naturals(case['legal_words_by_r'],k,'legal histogram'); bound=naturals(case['stars_bars'],k,'stars bars')
        actual_a,actual_legal=enumerate_prefix(d,k)
        check('prefix_inversion_histogram',a==actual_a)
        check('prefix_legal_histogram',legal==actual_legal)
        check('prefix_exhaustive_factorial',sum(a)==factorial(k))
        check('prefix_recurrence_crosscheck',sum(legal)==by_d[d][k])
        D=d*k
        block=[comb(D+t-1,t) for t in range(k+1)]
        conv=[1]+[0]*k
        for r in range(k):
            conv=[sum(conv[j]*block[t-j] for j in range(t+1)) for t in range(k+1)]
            formula=comb(D*(r+1)+k-1,k)
            check('prefix_stars_bars_formula',bound[r]==formula)
            check('prefix_block_convolution',conv[k]==formula)
            check('prefix_exact_entropy_bound',legal[r]<=a[r]<=bound[r])
        COUNTS['prefix_cases']+=1

def recurrence_checks(cases,base):
    for row,d in zip(cases,CDS):
        keys(row,('d','counts'),'recurrence case'); equal(integer(row['d'],'d'),d,'ordered count inventory')
        values=naturals(row['counts'],CN+1,'recurrence counts')
        check('difference_incoming_recurrence',values==incoming_counts(d))
        check('recurrence_empty_and_singleton',values[:2]==[1,1])
        for n in range(1,CN+1):
            check('count_positive_monotone',0<values[n-1]<=values[n])
            check('count_inversion_upper_bound',values[n]<=factorial(n))
            if d>=n-1: check('large_d_factorial_endpoint',values[n]==factorial(n))
        if d==0: check('d0_fishburn_endpoint',values==base['zero_level']['fishburn'][:CN+1])
        if d==1: check('d1_weak_count_agreement',values==list(map(sum,base['level_polynomials'])))
        # Independent definition-only enumeration for d=0 as the prefix transform is d>=1.
        if d==0:
            for n in range(1,PN+1):
                actual=sum(all(x[i]<=1+sum(x[t+1]>x[t] for t in range(i-1)) for i in range(1,n)) for x in product(*(range(i) for i in range(1,n+1))))
                check('d0_independent_enumeration',actual==values[n])
        COUNTS['recurrence_parameters']+=1

def run(path):
    global CURRENT_PHASE
    COUNTS.clear(); CURRENT_PHASE='preflight'
    raw,data=load_json(path); schema(data)
    CURRENT_PHASE='weighted_exact_algebra'
    weak_result=weak.run(HERE/'weak_fixtures.json')
    _,weak_expected=load_json(HERE/'weak_expected_summary.json'); equal(weak_result,weak_expected,'preserved report107 expected summary')
    _,base=load_json(HERE/'weak_fixtures.json')
    CURRENT_PHASE='shifted_exact_algebra'; shifted_checks(data['shifted_cases'],base)
    CURRENT_PHASE='capped_exact_algebra'; capped_checks(data['capped_cases'])
    CURRENT_PHASE='crossing_exact_algebra'; crossing_checks(data['crossing_cases'])
    CURRENT_PHASE='integer_recurrences'; recurrence_checks(data['recurrences'],base)
    CURRENT_PHASE='exhaustive_prefixes'; prefix_checks(data['prefix_cases'],data['recurrences'])
    return {'status':'passed','arithmetic':'integers_and_exact_rationals_only','scope':data['scope'],'fixture_sha256':sha256(raw).hexdigest(),'preserved_weighted_summary':weak_result,'checks':dict(sorted(COUNTS.items()))}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures',type=Path,default=HERE/'fixtures.json')
    parser.add_argument('--expected-summary',type=Path,default=HERE/'expected_summary.json')
    args=parser.parse_args()
    try:
        result=run(args.fixtures)
        global CURRENT_PHASE
        CURRENT_PHASE='expected_summary'
        _,expected=load_json(args.expected_summary); equal(result,expected,'committed expected summary')
    except Exception as error:
        print(json.dumps({'status':'failed','phase':CURRENT_PHASE,'error_type':type(error).__name__,'error':str(error),'python_optimization':sys.flags.optimize},sort_keys=True),file=sys.stderr)
        return 1
    print(json.dumps({**result,'python_optimization':sys.flags.optimize},sort_keys=True)); return 0
if __name__=='__main__': sys.exit(main())
