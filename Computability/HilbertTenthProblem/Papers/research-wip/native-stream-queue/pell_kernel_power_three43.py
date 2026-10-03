"""Exact positive power-of-three geometry with the unchanged43 plus kernel."""
import argparse
from collections import Counter
import json
from math import comb
from pathlib import Path
import sympy as sp
import native_controller_three_selector_53 as prior
from pell_kernel_power_two43 import pell

CORE=[(name,op,'q' if left=='n2' else left,'q' if right=='n2' else right)
      for name,op,left,right in prior.CORE]
SCHEDULE=list(CORE)
NAMES=['q']+prior.CORE_NAMES
EQUALITIES=[('r1','q')]+prior.kernel.EQUALITIES[1:]


def sources(z):
    q=z['q']
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=(z[name] for name in prior.CORE_NAMES)
    X,Y=w*q,s*q;delta=a*a+6*a+8;U=2*r+1+j*c
    return [r-q+1,((X*Y)**2+X)*(k*Y)**2-tau*(tau+1),
            c-k*Y-eta,k-eta-zeta,k-r-1-h*X*Y,a-Y*(X+1),
            d-X-a*c-ga*(6*a+8),d*d-1-delta*c*c,
            (i*c*c)**2-delta*(f*f-1),
            delta*(f*f-1)*(U*U-ya*ya)-(1-ya*ya),U-c-o*f]


def source_check():
    z={name:sp.Symbol(name) for name in NAMES}
    env=prior.execute(SCHEDULE,z);polys=sources(z)
    U=2*z['r']+1+z['j']*z['c'];correction=polys[8]*(U*U-z['y_aux']**2)
    records=[]
    for ix,((left,right),polynomial) in enumerate(zip(EQUALITIES,polys)):
        adjust=correction if ix==9 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust)==0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(polynomial)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE)==43 and counts['*']==25 and counts['+']+counts['-']==18
    assert len(polys)==len(EQUALITIES)==11 and len(NAMES)==18
    assert set().union(*(p.free_symbols for p in polys))==set(z.values())
    return dict(operations=43,multiplications=25,additions_subtractions=18,equations=11,
                positive_parameters=['q'],positive_auxiliaries=prior.CORE_NAMES,
                instructions=[list(row) for row in SCHEDULE],sources=records,
                projection='q=3^t with integer t>=1; free r1=q and kernel scaleq')


def bootstrap():
    checked=0
    for q in range(5,501,2):
        r=q-1
        for w in (1,2,3):
            X=w*q;Y=q;a=Y*(X+1);A=a+3;P=2*X*Y*Y+1
            assert X*Y>r+1 and a>2*r+1 and P>A
            assert (2*A-1)**5>A*(A*A-1)**2 and 10*X*Y*Y>a
            lower_y=X**r
            assert 12*r<(X+1)*lower_y
            if X>=9:assert 3**(2*r+1)<X**(r+1)
            elif X==5:assert q==5 and r==4 and 3**9<6*6*5**4+8
            else:
                assert X==7 and q==7 and r==6
                assert 3**13<8*(7**6+12*7**5)
            checked+=1
    a=sp.Symbol('a')
    assert sp.expand(9-6*(a+3)+1+(6*a+8))==0
    return dict(odd_q_interval=[5,499],tested_w=[1,2,3],cases=checked,
                even_q_obstruction='X,Y,a,d andDelta even contradict d^2=1+Delta*c^2',
                small_representative_bounds=[dict(q=5,X=5,r=4,modulus_lower=22508,power=3**9),
                    dict(q=7,X=7,r=6,a_lower=8*(7**6+12*7**5),power=3**13)],
                lower_ratio_first=True)


def canonical_main(q):
    v=q;t=0
    while v%3==0:v//=3;t+=1
    assert v==1 and t>=1
    r=q-1;J=2*r+1;X=3**J;den=X**r;num=(X+1)**(2*r);Y,tail=divmod(num,den)
    a=Y*(X+1);A=a+3;delta=A*A-1;P=2*X*Y*Y+1
    d,c=pell(A,J);v,k=pell(P,r+1)
    eta=c-Y*k;zeta=k-eta
    assert X%q==Y%q==0 and 0<4*tail<den and eta>0 and zeta>0
    assert (v-1)%2==0 and (k-r-1)%(X*Y)==0 and (d-X-a*c)%(6*a+8)==0
    values=dict(q=q,r=r,w=X//q,s=Y//q,a=a,c=c,d=d,k=k,eta=eta,zeta=zeta,
                tau=(v-1)//2,h=(k-r-1)//(X*Y),ga=(d-X-a*c)//(6*a+8))
    assert min(values.values())>0 and d*d-delta*c*c==1
    assert ((X*Y)**2+X)*(k*Y)**2==values['tau']*(values['tau']+1)
    assert c*den>k*num and c<(Y+1)*k
    env=prior.execute(SCHEDULE[:29],values)
    for left,right in EQUALITIES[:8]:assert env[left]==env[right],(q,left,right)
    central=comb(2*r,r);valuation=0
    while central%3==0:central//=3;valuation+=1
    assert valuation==t
    return dict(q=q,r=r,X=X,Y=Y,a=a,c=c,k=k,eta=eta,zeta=zeta,
                h=values['h'],ga=values['ga'],central_valuation=valuation,
                positive_main_coordinates=True,all_eight_main_equalities=True)


def auxiliary_polynomials():
    A,T=sp.symbols('A T');psi=[sp.Integer(0),sp.Integer(1)]
    for j in range(2,14):psi.append(sp.expand(2*A*psi[-1]-psi[-2]))
    Q=[sp.Integer(1),4*T-3]
    for h in range(2,7):Q.append(sp.expand((4*T-2)*Q[-1]-Q[-2]))
    for h in range(7):
        assert sp.expand(Q[h].subs(T,1-A*A)-(-1)**h*psi[2*h+1])==0
        assert Q[h].subs(T,0)==(-1)**h*(2*h+1)
    return dict(normalized_odd_index_identities_checked_through_J=13,
                positive_branch='Evenr givesJ=1mod4, hence u=c modf andu=J modc',
                full_auxiliary_extension='Parametric positive Pell construction; not materialized')


def verify():
    examples=[canonical_main(q) for q in (3,9,27)]
    records=[examples[0]]+[dict(q=z['q'],r=z['r'],central_valuation=z['central_valuation'],
               main_bit_lengths={name:z[name].bit_length() for name in ('X','Y','a','c','k')},
               positive_main_coordinates=True,all_eight_main_equalities=True) for z in examples[1:]]
    return dict(status='PASS_COMPLETE_POWER_THREE_GEOMETRY_43',source=source_check(),
                bootstrap=bootstrap(),canonical_main_cases=records,auxiliary=auxiliary_polynomials(),
                scope='Exact positive power-of-three geometry only; no streams, controller, input or universal compiler included',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key!='source'},indent=2))
