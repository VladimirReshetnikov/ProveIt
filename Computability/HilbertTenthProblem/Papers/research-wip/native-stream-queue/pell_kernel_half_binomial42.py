"""Strong42 half-binomial kernel and a75-operation compiler-source ledger.

The kernel projection is proved under explicit external bounds. The full75
compiler/encoding proof is not part of this packet.
"""
import argparse
from collections import Counter
from math import comb, isqrt
import json
from pathlib import Path
import sys
import sympy as sp

VERIFICATION=Path(__file__).resolve().parents[2]/'verification'
sys.path.insert(0,str(VERIFICATION))
import explore_fixed_raw_universal_76 as complete
import pell_kernel_power_two43 as binary
import complete75_half_binomial as candidate75

CORE_NAMES=['a','c','d','f','h','i','j','k','o','s','w','tau','eta','zeta','ga','y_aux']
EQUALITIES=complete.EQUALITIES[5:15]


def change(rows):
    answer=[]
    for name,op,left,right in rows:
        if name=='tr1':continue
        if name=='tauplus1':answer.append(('tau_square','*','tau','tau'))
        elif name=='R9':answer.append((name,'-','tau_square',1))
        elif name=='H17':answer.append((name,op,left,'r'))
        else:answer.append((name,op,left,right))
    return answer


CORE=change(complete.CORE)


def run(rows,env):
    env=dict(env)
    for name,op,left,right in rows:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def sources(z):
    X=z['w']*z['scale'];Y=z['s']*z['scale'];E=X*Y
    a,c,d,f,h,i,j,k,o,s,w,tau,eta,zeta,ga,y=(z[n] for n in CORE_NAMES)
    R=z['R'];delta=a*a+4*a+3;U=j*c-R
    return [((E*E)+X)*(k*Y)**2-tau*tau+1,
            c-k*Y-eta,k-eta-zeta,k-R-1-h*E,a-Y*(X+1),
            d-X-a*c-ga*(4*a+3),d*d-1-delta*c*c,
            (i*c*c)**2-delta*(f*f-1),
            delta*(f*f-1)*(U*U-y*y)-1+y*y,U-o*f+c]


def source_check():
    names=['scale','R']+CORE_NAMES
    z={name:sp.Symbol(name) for name in names}
    env=run(CORE,dict(z,n2=z['scale'],r=z['R']))
    polys=sources(z);U=z['j']*z['c']-z['R']
    correction=polys[7]*(U*U-z['y_aux']**2)
    records=[]
    for ix,((left,right),p) in enumerate(zip(EQUALITIES,polys)):
        adjust=correction if ix==8 else 0
        actual=sp.expand(env[left]-env[right]);sign=1 if sp.expand(actual-p-adjust)==0 else -1
        assert sp.expand(actual-sign*p-adjust)==0,ix
        records.append(dict(equality=[left,right],source_sign=sign,source=str(sp.expand(p)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in CORE)
    assert len(CORE)==42 and counts['*']==25 and counts['+']+counts['-']==17
    assert len(EQUALITIES)==len(polys)==10 and len(CORE_NAMES)==16
    assert set().union(*(p.free_symbols for p in polys))==set(z.values())
    old=Counter(row[1] for row in complete.CORE)
    assert len(complete.CORE)==43 and old['*']==25 and old['+']+old['-']==18
    return dict(operations=42,multiplications=25,additions_subtractions=17,equations=10,
                positive_parameters=['scale','R'],positive_auxiliaries=CORE_NAMES,
                aliases={'n2':'scale','r':'R','k':'K (twice the first Pell psi coefficient)'},
                instructions=[list(row) for row in CORE],sources=records,
                deleted_instruction=['tr1','+','r1','r'],
                replaced_norm_instructions=[['tau_square','*','tau','tau'],['R9','-','tau_square',1]],
                retained_strong_auxiliary_square=True,
                theorem_external_hypotheses='q>=16, scale=q^3, 3q+1<=R<q^4; construction of scale and bounds is separately paid',
                exact_projection='q=2^t, R=3 mod4, popcount((R-1)/2)>=3t+1, under displayed external bounds')


def candidate75_source():
    result=candidate75.source_audit()
    assert result['schedule']==[list(row) for row in change(complete.SCHEDULE)]
    assert result['operations']==75 and result['multiplications']==41 and result['additions_subtractions']==34
    return dict(operations=75,multiplications=41,additions_subtractions=34,equations=19,
                positive_existentials_excluding_x=30,
                source_dependency='complete75_half_binomial.source_audit',
                fixed_mask_alias=result['fixed_mask_alias'],
                entire_schedule_matches_kernel_edits=True,
                ledger={'outer':19,'half_binomial_kernel':42,'input_bridge':14},
                scope='Literal candidate ledger only: modified compiler, mask, synchronization and ordinary-input theorem are pending outside this packet')


def bootstrap_checks():
    cases=0
    for q in range(16,81):
        for R in {3*q+1,3*q+2,q*q,q**4-1}:
            if not 3*q+1<=R<q**4:continue
            X=Y=q**3;E=X*Y;a=Y*(X+1);A=a+2;P=2*X*Y*Y+1
            assert E>2*R and a>R and P>A and 6*X*Y*Y>a
            n=(R+2)//2;p=n+1
            assert n>=(R+1)/2 and p>=6 and Y*(R+1)>2*R
            assert (2*A-1)**5>A*(A*A-1)**2
            assert 4*((R-1)//2)<a//2
            if R%2:
                r=(R-1)//2
                # Integer-equivalent comparisons for the exponent representatives.
                assert r>=24 and X>=4096
                # X/64>=64 and X/24>1 imply the first comparison for all r>=0.
                assert X>=64 and X>24 and X**2>3
                # These inequalities prove 24*64^r<X^(r+1) and 3X^3<X^(r+1),
                # without constructing exponentially large test integers.
            cases+=1
    return dict(prepower_parameter_cases=cases,q_range=[16,80],
                lower_R='3q+1, not q^2; packed boundary is allowed before typing')


def first_norm_checks():
    cases=0
    for V in range(1,201):
        D=V*(V+1);P=2*V+1
        assert V*V<D<(V+1)**2
        assert V*V<D+1<(V+1)**2
        assert P*P-4*D==1
        for n in range(1,11):
            T,k=binary.pell(P,n);K=2*k
            assert T*T-D*K*K==1
            cases+=1
    # Exhaust every positive coefficient in a small rectangle, not just generated paths.
    arbitrary=solutions=0
    for V in range(1,41):
        D=V*(V+1);P=2*V+1
        generated=set()
        n=1
        while True:
            T,k=binary.pell(P,n)
            if 2*k>200:break
            generated.add((T,2*k));n+=1
        for K in range(1,201):
            squared=1+D*K*K;T=isqrt(squared)
            if T*T==squared:
                assert K%2==0 and (T,K) in generated
                solutions+=1
            arbitrary+=1
    return dict(generated_pell_points=cases,arbitrary_coefficients=arbitrary,
                admitted=solutions,fundamental_pair='(2V+1,2) for every V>=1')


def canonical_main(R,scale=1):
    assert R>=3 and R%4==3
    r=(R-1)//2;X=2**R;den=X**r;num=(X+1)**(2*r);M,tail=divmod(num,den)
    assert M%2==0 and 0<4*tail<den
    Y=M//2
    assert X%scale==Y%scale==0
    a=Y*(X+1);A=a+2;P=2*X*Y*Y+1
    d,c=binary.pell(A,R);T,k=binary.pell(P,r+1);K=2*k
    eta=c-K*Y;zeta=K-eta;h,rem=divmod(K-R-1,X*Y)
    ga,rem_ga=divmod(d-X-a*c,4*a+3)
    assert rem==rem_ga==0 and min(eta,zeta,h,ga)>0
    assert c*den>k*num and c*den<k*(num+den)
    values=dict(scale=scale,R=R,w=X//scale,s=Y//scale,a=a,c=c,d=d,k=K,
                tau=T,eta=eta,zeta=zeta,h=h,ga=ga)
    env=run(CORE[:28],dict(values,r=R,n2=scale))
    for left,right in EQUALITIES[:7]:assert env[left]==env[right],(R,left,right)
    return values


def materialized_complete():
    # A real full42 tuple, but outside the q>=16 theorem domain; not a full75 tuple.
    values=canonical_main(3);A=values['a']+2;delta=A*A-1;c=values['c'];R=values['R'];m=2*c*R
    f,v=binary.pell(A,m);i,rem=divmod(delta*v,c*c);assert rem==0
    auxiliary=i*c*c;chi,y=binary.pell(auxiliary,R);U,rem=divmod(chi,auxiliary);assert rem==0
    o,rem_o=divmod(U+c,f);j,rem_j=divmod(U+R,c);assert rem_o==rem_j==0
    values.update(f=f,i=i,y_aux=y,o=o,j=j)
    assert set(values)==set(['scale','R']+CORE_NAMES) and min(values.values())>0
    env=run(CORE,dict(values,r=R,n2=values['scale']))
    for left,right in EQUALITIES:assert env[left]==env[right],(left,right)
    return dict(R=R,scale=1,X=8,Y=5,a=values['a'],c=c,K=values['k'],tau=values['tau'],
                eta=values['eta'],zeta=values['zeta'],h=values['h'],auxiliary_index=m,
                all_ten_equalities=True,all_supplied_coordinates_positive=True,
                coordinate_bit_lengths={n:v.bit_length() for n,v in values.items()},
                scope='Full numerical42 prototype outside the q>=16 projection hypotheses; compiler witnesses not materialized')


def ratio_and_valuation_checks():
    main=[]
    for R in (3,7,11,15,19,23,31):
        v=canonical_main(R)
        main.append(dict(R=R,old_r=(R-1)//2,Y_bits=v['s'].bit_length(),
                         main_coordinate_bits={name:v[name].bit_length() for name in ('a','c','d','k')},
                         all_seven_main_equations=True,strict_positive_eta_zeta=True))
    cases=0
    for r in range(1,101):
        R=2*r+1;X=2**R;den=X**r;M,tail=divmod((X+1)**(2*r),den);Y=M//2
        assert M%2==0 and 0<4*tail<den
        cb=comb(2*r,r)
        val=lambda n:(n&-n).bit_length()-1
        assert val(cb)==r.bit_count() and val(Y)==r.bit_count()-1
        for t in range(1,8):
            assert (Y%(2**(3*t))==0)==(r.bit_count()>=3*t+1)
            cases+=1
    return dict(main_prototypes=main,half_binomial_threshold_cases=cases,
                prototype_scope='Exact main equations with scale1; general-q theorem proved parametrically')


def verify():
    return dict(status='PASS_STRONG_HALF_BINOMIAL_KERNEL42',kernel=source_check(),
                candidate75=candidate75_source(),bootstrap=bootstrap_checks(),
                first_norm=first_norm_checks(),ratios=ratio_and_valuation_checks(),
                complete_prototype=materialized_complete(),
                scope='Proved42 kernel under explicit external bounds;75 source ledger is not a complete compiler theorem',
                established_complete_universal_bound=75)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('kernel','candidate75')},indent=2))
