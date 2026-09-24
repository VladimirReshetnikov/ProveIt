#!/usr/bin/env python3
"""69 operations for the exact cyclic Rule110 relation in radix16.

Supplied parameters q,P,C retain their roles but change numerical radix
relative to the separate radix128 certificate71. No universal interface.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

import explore_rule110_cyclic_certificate as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
B=16
PARAMETERS=list(previous.PARAMETERS)
OUTER_NAMES=list(previous.OUTER_NAMES)
CORE_NAMES=list(previous.CORE_NAMES)
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}
OUTER=[
    ('qm1','-','q',1),('repunit','*',15,'Jrep'),
    ('Pv','*','P','v'),('Pm1','-','P',1),('alignment','*',15,'align'),
    ('C2','+','C','C'),('bounded','+','C2','alpha'),
    ('kp','*',67,'P'),('kinner','+','kp',3),('innerC','*','kinner','C'),
    ('transport_gap','-','innerC','F'),('Pgap','*','P','transport_gap'),
    ('CJ','+','C','Jrep'),('local_lhs','+','Pgap','CJ'),('local_rhs','*','zquot','qm1'),
    ('Lbig','*','q','q'),('n2','*','Lbig','q'),
    ('qF','*','q','F'),('packed','+','C2','qF'),
    ('m4q','*',4,'q'),('mask_factor','+','m4q',13),('mask','*','mask_factor','Jrep'),
    ('gap','-','Lbig','packed'),('Lm1','-','Lbig',1),
    ('rproduct','*','gap','Lm1'),('r_lhs','+','rproduct','mask'),
]
CORE=list(previous.CORE)
SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('repunit','qm1'),('Pv','q'),('alignment','Pm1'),
                  ('bounded','q'),('local_lhs','local_rhs'),('r','r_lhs')]
EQUALITIES=OUTER_EQUALITIES+previous.retained.retained.CORE_EQUALITIES


def source_residuals():
    z=SYM
    q,P,C=[z[name] for name in PARAMETERS]
    v,J,align,F,alpha,zquot=[z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=[z[name] for name in CORE_NAMES]
    L=q*q;scale=q**3;S=2*C+q*F;M=(4*q+13)*J
    X=w*scale;Y=s*scale;Delta=a*a+4*a+3;auxu=j*c-(2*r+1)
    K=1+P*(3+67*P)
    return [15*J-q+1,P*v-q,15*align-P+1,2*C+alpha-q,
            K*C+J-P*F-zquot*(q-1),r-(L-S)*(L-1)-M,
            X*Y*Y*(X*Y*Y+1)*k*k-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(4*a+3),d*d-Delta*c*c-1,
            (i*c*c)**2-Delta*(f*f-1),
            Delta*(f*f-1)*(auxu*auxu-ya*ya)-(1-ya*ya),auxu+c-o*f]


def verify_source():
    env=dict(SYM);histogram=baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(u*u-SYM['y_aux']**2);records=[]
    for index,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if index==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==26 and len(CORE)==43 and len(primitives)==69
    assert counts=={'+':31,'*':38}
    assert len(EQUALITIES)==len(sources)==16
    assert len(NAMES)==len(set(NAMES))==26 and len(OUTER_NAMES+CORE_NAMES)==23
    assert Counter(row[1] for row in OUTER)=={'*':13,'+':8,'-':5}
    assert sp.expand(env['n2']-SYM['q']**3)==0
    assert all(p.free_symbols<=set(SYM.values()) for p in sources)
    assert set(NAMES)<=({x for row in SCHEDULE for x in row[2:]}
                        |{x for pair in EQUALITIES for x in pair})
    return dict(operations=69,multiplications=38,additions_subtractions=31,
                outer_operations=26,kernel_operations=43,parameters=PARAMETERS,
                positive_unknown_count=23,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                positive_coordinates_including_parameters=26,equations=16,
                primitive_instructions=primitives,histogram=histogram,sources=records,
                kernel_scale='q^3; no square-scale assumption before power decoding',
                kernel_sign='fixed minus; actual r is odd',
                ledger={'geometry':5,'bound_sharing_C2':1,'local_positive_quotient':8,
                        'packing_including_two_powers_and_C2':12})


def word(bits):
    return sum(bit*B**i for i,bit in enumerate(bits))


def numeric_outer(values):
    env=dict(values)
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left;bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def verify_scalar():
    cases=[]
    for l,c,r,y in product((0,1),repeat=4):
        value=1+l+3*c+3*r+4*y
        actual=y==((110>>(4*l+2*c+r))&1)
        assert 1<=value<=12<B-1 and (value&4==0)==actual
        if actual:assert y<=c+r
        cases.append(dict(bits=[l,c,r,y],value=value,accepted=actual))
    return dict(cases=cases,scalar_cases=16,maximum_value=12)


def verify_words():
    cases=accepted=0;all_signs=Counter();valid_signs=Counter();records=[]
    for N in range(1,13):
        q=B**N;D=q-1;J=D//15;L=q*q;M=(4*q+13)*J
        assert 0<M<L-1 and M.bit_count()==4*N
        for raw in range(1,1<<N):
            bits=[raw>>i&1 for i in range(N)];C=word(bits)
            for hh in range(1,N+1):
                P=B**hh;align=(P-1)//15
                left=[bits[(i+hh)%N] for i in range(N)]
                right=[bits[(i-hh)%N] for i in range(N)]
                nxt=[bits[(i-hh-1)%N] for i in range(N)]
                LL,RR,YY=map(word,(left,right,nxt))
                F=J+LL+3*C+3*RR+4*YY
                actual=all(nxt[i]==((110>>(4*left[i]+2*bits[i]+right[i]))&1) for i in range(N))
                assert 0<F<D and 0<2*C<q
                K=1+P*(3+67*P);z,rem=divmod(K*C+J-P*F,D);assert rem==0
                sign='positive' if z>0 else 'negative' if z<0 else 'zero';all_signs[sign]+=1
                kL=(P*LL-C)//D;kR=(P*C-RR)//D;kY=(B*P*C-YY)//D
                assert 0<=kL<P and kR>=0 and kY>=0
                assert z==P*(3*kR+4*kY)-kL-align
                S=2*C+q*F;r=(L-S)*(L-1)+M
                assert 0<S<L and r>=M>=64 and r*r>q**3 and r<q**4
                assert r%2==1 and r.bit_count()<=12*N
                assert (r.bit_count()==12*N)==(S&M==0)==actual
                cases+=1
                if not actual:continue
                accepted+=1;valid_signs[sign]+=1
                assert YY<=C+RR and kY>=1 and z>=4*P-(P-1)-align>0
                values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=align,F=F,
                            alpha=q-2*C,zquot=z,r=r)
                env=numeric_outer(values)
                assert min(values.values())>0
                assert all(env[aa]==env[bb] for aa,bb in OUTER_EQUALITIES)
                assert all(env[name]>0 for name,_,_,_ in OUTER)
                records.append(dict(N=N,h=hh,raw_word=raw,positive_outer=values,
                                    central_binomial_valuation=r.bit_count()))
    assert cases==90036 and accepted==33 and valid_signs=={'positive':accepted}
    return dict(cyclic_cases=cases,accepted=accepted,all_word_quotient_signs=dict(all_signs),
                accepted_quotient_signs=dict(valid_signs),accepted_outer_tuples=records,
                full_packed_Pell_tuples_materialized=False)


def verify_prebounds():
    candidates=positive=nonpower=0
    for align,v0 in product(range(1,17),range(7)):
        P=1+15*align;v=1+15*v0;q=P*v;J=(q-1)//15;L=q*q;M=(4*q+13)*J
        assert L-1-M==J*(11*q+2)>0 and 15*M>4*q*q
        assert M>=64 and M*M>q**3
        for C in (1,2,max(1,q//8),(q-1)//2):
            alpha=q-2*C
            if alpha<=0:continue
            for F in (1,2,q//2,q-1,q,q+1,2*q):
                candidates+=1;S=2*C+q*F;r=(L-S)*(L-1)+M
                if r<=0:continue
                positive+=1;nonpower+=bool(q&(q-1))
                assert 0<2*C<q and S<=L and F<q and S<L
                assert 64<=M<=r<q**4 and r>=q*q and r*r>q**3
                assert q**6>2*r+1 and 8*r<q**6
    return dict(candidates=candidates,positive_index_cases=positive,nonpower_q_cases=nonpower,
                strict_packed_bound_recovered_before_kernel=True)


def verify_inverse_carry():
    cases=overflow=0
    for exponent in range(1,10):
        L=1<<exponent
        for S in range(1,L):
            for M in range(L):
                r=(L-S)*(L-1)+M;threshold=exponent+M.bit_count()
                assert r.bit_count()<=threshold
                assert (r.bit_count()==threshold)==(S&M==0)
                if S+M>=L:
                    overflow+=1
                    valuation=(S&-S).bit_length()-1
                    defect=S.bit_count()+M.bit_count()-(S+M).bit_count()
                    assert r.bit_count()==threshold-defect-valuation
                    assert r.bit_count()<threshold
                else:
                    assert r.bit_count()==exponent-S.bit_count()+(S+M).bit_count()
                cases+=1
    field_cases=0
    for S in range(256):
        F,low=divmod(S,16)
        assert (S&77==0)==(low in (0,2) and F&4==0)
        field_cases+=1
    return dict(arbitrary_word_mask_pairs=cases,overflow_cases=overflow,one_cell_field_cases=field_cases)


def verify():
    return dict(status='PASS_RULE110_CYCLIC69',radix=B,source=verify_source(),scalar=verify_scalar(),
                prepower_bounds=verify_prebounds(),inverse_carry=verify_inverse_carry(),
                cyclic=verify_words(),pell=previous.verify_pell_components(),
                proof='../1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md',
                universal_certificate_improvement=False,
                scope='Exact positive radix16 certificate in supplied q,P,C for a nonzero cyclic Rule110 word; changed numerical representation from radix128; no universal input/marker/target interface')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          result['cyclic']['cyclic_cases'],'cyclic cases;',result['cyclic']['accepted'],'accepted')
