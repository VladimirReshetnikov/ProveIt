#!/usr/bin/env python3
"""Exact 71-operation positive certificate for a parametrized cyclic relation.

Parameters q,P,C are supplied. This is not a raw-input universal compiler
or a replacement for the distinct Rule110 finite-history endpoint system.
No enormous full packed Pell tuple is materialized.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

import explore_one_field_rule110_history as retained
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives
from round37_1980_base_two_pell_regression import pell_power

OUT=Path(__file__).with_suffix('.json')
B=128
PARAMETERS=['q','P','C']
OUTER_NAMES=['v','Jrep','align','F','alpha','zquot']
CORE_NAMES=list(retained.CORE_NAMES)
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}
OUTER=[
    ('qm1','-','q',1),('repunit','*',127,'Jrep'),
    ('Pv','*','P','v'),('Pm1','-','P',1),('alignment','*',127,'align'),
    ('CF','+','C','F'),('bounded','+','CF','alpha'),
    ('kp','*',23+42*B,'P'),('kinner','+','kp',23),
    ('pk','*','P','kinner'),('Klocal','+','pk',18),
    ('KC','*','Klocal','C'),('PF','*','P','F'),
    ('zD','*','zquot','qm1'),('local_rhs','+','PF','zD'),
    ('n','*','q','q'),('n2','*','n','n'),
    ('qF','*','q','F'),('S','+','C','qF'),
    ('m36q','*',36,'q'),('mask_factor','+','m36q',126),
    ('T','*','mask_factor','Jrep'),('Tplus','+','T',1),
    ('n2mn','-','n2','n'),('n2m1','-','n2',1),
    ('SA','*','S','n2mn'),('TB','*','Tplus','n2m1'),
    ('r_lhs','+','SA','TB'),
]
CORE=list(retained.CORE)
SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('repunit','qm1'),('Pv','q'),('alignment','Pm1'),
                  ('bounded','q'),('KC','local_rhs'),('r','r_lhs')]
EQUALITIES=OUTER_EQUALITIES+retained.retained.CORE_EQUALITIES


def source_residuals():
    z=SYM
    q,P,C=[z[name] for name in PARAMETERS]
    v,J,align,F,alpha,zquot=[z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=[z[name] for name in CORE_NAMES]
    n=q*q;S=C+q*F;Tplus=(36*q+126)*J+1
    X=w*n*n;Y=s*n*n;Delta=a*a+4*a+3
    auxu=j*c-(2*r+1)
    K=18+P*(23+(23+42*B)*P)
    return [127*J-q+1,P*v-q,127*align-P+1,C+F+alpha-q,
            K*C-P*F-zquot*(q-1),r-S*(n*n-n)-Tplus*(n*n-1),
            X*Y*Y*(X*Y*Y+1)*k*k-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(4*a+3),d*d-Delta*c*c-1,
            (i*c*c)**2-Delta*(f*f-1),
            Delta*(f*f-1)*(auxu*auxu-ya*ya)-(1-ya*ya),auxu+c-o*f]


def verify_source():
    env=dict(SYM)
    histogram=baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals()
    auxu=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(auxu**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right])
        adjust=correction if index==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==28 and len(CORE)==43 and len(primitives)==71
    assert counts=={'+':31,'*':40}
    assert len(EQUALITIES)==len(sources)==16
    assert len(NAMES)==len(set(NAMES))==26 and len(OUTER_NAMES+CORE_NAMES)==23
    assert set(NAMES)<=({x for row in SCHEDULE for x in row[2:]}
                        |{x for pair in EQUALITIES for x in pair})
    assert all(p.free_symbols<=set(SYM.values()) for p in sources)
    assert sp.expand(env['n2']-SYM['q']**4)==0
    assert Counter(row[1] for row in OUTER)=={'*':15,'+':9,'-':4}
    return dict(operations=71,multiplications=40,additions_subtractions=31,
                outer_operations=28,kernel_operations=43,parameters=PARAMETERS,
                positive_unknown_count=23,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                positive_coordinates_including_parameters=26,equations=16,
                primitive_instructions=primitives,histogram=histogram,sources=records,
                kernel_sign='fixed minus; actual packed r is odd',
                ledger={'geometry':5,'bound':2,'local_positive_quotient':8,'packing_including_two_powers':13})


def word(bits):
    return sum(bit*B**i for i,bit in enumerate(bits))


def numeric_outer(values):
    env=dict(values)
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left
        bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def verify_scalar():
    cases=[]
    for l,c,r,y in product((0,1),repeat=4):
        value=18*l+23*c+23*r+42*y
        actual=y==((110>>(4*l+2*c+r))&1)
        assert 0<=value<=106<B-1 and (value&36==0)==actual
        if actual:assert y<=c+r
        cases.append(dict(bits=[l,c,r,y],value=value,accepted=actual))
    return dict(cases=cases,scalar_cases=16,maximum_value=106,
                necessary_output_bound='y <= center + right')


def verify_words():
    cases=accepted=0
    all_signs=Counter();valid_signs=Counter();records=[]
    for N in range(1,13):
        q=B**N;D=q-1;J=D//127;n=q*q;T=(36*q+126)*J;Tplus=T+1
        assert 0<Tplus<n and Tplus%2==1
        for raw in range(1,1<<N):
            bits=[raw>>i&1 for i in range(N)];C=word(bits)
            for hh in range(1,N+1):
                P=B**hh
                left=[bits[(i+hh)%N] for i in range(N)]
                right=[bits[(i-hh)%N] for i in range(N)]
                nxt=[bits[(i-hh-1)%N] for i in range(N)]
                LL,RR,YY=map(word,(left,right,nxt))
                F=18*LL+23*C+23*RR+42*YY
                actual=all(nxt[i]==((110>>(4*left[i]+2*bits[i]+right[i]))&1) for i in range(N))
                assert 0<F<D and C+F<q
                K=18+P*(23+(23+42*B)*P)
                z,rem=divmod(K*C-P*F,D)
                assert rem==0
                sign='positive' if z>0 else 'negative' if z<0 else 'zero'
                all_signs[sign]+=1
                kL=(P*LL-C)//D;kR=(P*C-RR)//D;kY=(B*P*C-YY)//D
                assert 0<=kL<P and kR>=0 and kY>=0
                assert z==P*(23*kR+42*kY)-18*kL
                S=C+q*F;r=S*(n*n-n)+Tplus*(n*n-1)
                assert n-S==(q-1)*C+q*(q-C-F)>0
                assert n-Tplus==J*((B-37)*q+1)>0
                assert n<=r<2*n**3 and r%2==1
                assert r.bit_count()==4*7*N-(S.bit_count()+T.bit_count()-(S+T).bit_count())
                assert (r.bit_count()>=4*7*N)==(S&T==0)==actual
                cases+=1
                if not actual:continue
                accepted+=1;valid_signs[sign]+=1
                assert YY<=C+RR and kY>=1 and z>=24*P+18>0
                values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=(P-1)//127,
                            F=F,alpha=q-C-F,zquot=z,r=r)
                assert min(values.values())>0
                env=numeric_outer(values)
                assert all(env[aa]==env[bb] for aa,bb in OUTER_EQUALITIES)
                assert all(env[name]>0 for name,_,_,_ in OUTER)
                records.append(dict(N=N,h=hh,raw_word=raw,positive_outer=values,
                                    central_binomial_valuation=r.bit_count()))
    assert cases==90036 and accepted>0 and valid_signs=={'positive':accepted}
    return dict(cyclic_cases=cases,accepted=accepted,all_word_quotient_signs=dict(all_signs),
                accepted_quotient_signs=dict(valid_signs),accepted_outer_tuples=records,
                full_packed_Pell_tuples_materialized=False)


def verify_prebounds():
    cases=nonpower=0
    for align,v0 in product(range(1,13),range(6)):
        P=1+127*align;v=1+127*v0;q=P*v;J=(q-1)//127;n=q*q
        for C in (1,2,q//5,q-3):
            for F in (1,2,max(1,(q-C)//2),q-C-1):
                alpha=q-C-F
                if alpha<=0:continue
                S=C+q*F;Tplus=(36*q+126)*J+1
                r=S*(n*n-n)+Tplus*(n*n-1)
                assert n-S==(q-1)*C+q*alpha>0
                assert n-Tplus==J*((B-37)*q+1)>0
                assert n>=64 and n<=r<2*n**3
                assert n**4>2*r+1 and 8*r<n**4
                cases+=1;nonpower+=bool(q&(q-1))
    return dict(cases=cases,nonpower_q_cases=nonpower)


def verify_carry():
    cases=overflow=0
    for exponent in range(1,8):
        n=1<<exponent
        for S in range(1,n):
            for T in range(n-1):
                r=S*(n*n-n)+(T+1)*(n*n-1)
                defect=S.bit_count()+T.bit_count()-(S+T).bit_count()
                assert r.bit_count()==2*exponent-defect
                assert defect>=0 and (defect==0)==(S&T==0)
                cases+=1;overflow+=S+T>=n
    return dict(arbitrary_word_pairs=cases,overlapping_top_sum_cases=overflow)


def verify_pell_components():
    main=[]
    for r in (3,7,15,31,65):
        Jidx=2*r+1;X=1<<Jidx
        numerator=(X+1)**(2*r);denominator=X**r
        Y,tail=divmod(numerator,denominator)
        a=Y*(X+1);A=a+2;Delta=A*A-1;E=X*Y;Q=X*Y*Y;P0=2*Q+1
        d,c=pell_power(A,Jidx);chi,k=pell_power(P0,r+1)
        eta=c-Y*k;zeta=k-eta
        h,remh=divmod(k-r-1,E);tau,remt=divmod(chi-1,2)
        ga,remg=divmod(d-X-a*c,4*a+3)
        assert min(eta,zeta,h,tau,ga)>0 and remh==remt==remg==0
        assert d*d-Delta*c*c==1 and X*Y*Y*(X*Y*Y+1)*k*k==tau*(tau+1)
        assert 4*tail<denominator and c*denominator>k*numerator
        assert (c*denominator-k*numerator)*(X+1)<16*r*k*denominator
        main.append(dict(r=r,main_index=Jidx,c_bits=c.bit_length(),positive_main_quotients=True))
    auxiliary=[]
    for A,Jidx in ((2,3),(2,7),(3,3),(4,3),(5,3)):
        _,c=pell_power(A,Jidx);Delta=A*A-1;m=2*c*Jidx
        f,psim=pell_power(A,m);RR=Delta*psim
        i,remi=divmod(RR,c*c);chi,y=pell_power(RR,Jidx);u,remu=divmod(chi,RR)
        j,remj=divmod(u+Jidx,c);o,remo=divmod(u+c,f)
        assert remi==remu==remj==remo==0 and min(i,j,o,y)>0
        assert RR*RR==Delta*(f*f-1) and RR*RR*(u*u-y*y)==1-y*y
        assert u==j*c-Jidx==o*f-c
        auxiliary.append(dict(A=A,main_index=Jidx,positive_minus_quotients=True))
    return dict(main_cases=main,auxiliary_cases=auxiliary,
                scope='Separate exact component regressions; not full enormous packed tuples')


def verify():
    return dict(status='PASS_RULE110_CYCLIC71',radix=B,source=verify_source(),
                scalar=verify_scalar(),prepower_bounds=verify_prebounds(),
                carry_identity=verify_carry(),cyclic=verify_words(),pell=verify_pell_components(),
                proof='../1980/EXPLORATION_RULE110_CYCLIC_CERTIFICATE.md',
                universal_certificate_improvement=False,
                scope='Exact positive certificate in supplied q,P,C for a nonzero Rule110 cyclic word with strides h,h+1; no raw-input/marker/target interface')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          result['cyclic']['cyclic_cases'],'cyclic cases;',result['cyclic']['accepted'],'accepted')
