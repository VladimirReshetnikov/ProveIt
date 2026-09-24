#!/usr/bin/env python3
"""Unique Start at67 operations, plus a conditional four-op endpoint pin."""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

import explore_three_cell_marked as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NAMES=list(previous.NAMES);CONSTANTS=list(previous.CONSTANTS);SYM=dict(previous.SYM)
MARKER=[row for row in previous.OUTER if row[0] in ('Bmarker_tail','marked_rhs')]
OUTER=[]
for row in previous.OUTER:
    if row in MARKER:continue
    if row[0]=='qF':OUTER.extend(MARKER)
    if row[0]=='packed':row=('packed','+','Bmarker_tail','qF')
    OUTER.append(row)
CORE=list(previous.CORE);SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=list(previous.OUTER_EQUALITIES);EQUALITIES=list(previous.EQUALITIES)
PIN=[('endpoint_scale','*','CE','W'),('endpoint_tail','*','endpoint_scale','Tend'),
     ('endpoint_rhs','+','Lend','endpoint_tail'),('endpoint_remainder_bound','+','Lend','betaend')]


def source_residuals():
    z=SYM;q,P,C,F,J=[z[name] for name in ('q','P','C','F','Jrep')]
    return [(z['B']-1)*J-q+1,P*z['v']-q,(z['B']-1)*z['align']-P+1,C+z['alpha']-q,
            (z['DC']+(z['DR']+z['B']*z['DY'])*P)*C-F-z['zquot']*(q-1),
            z['r']-(q*q-z['B']*z['Tmarker']-q*F)*(q*q-1)-(z['MC']+q*z['MF'])*J,
            C-2-z['B']*z['Tmarker']]+previous.four.previous.source_residuals()[6:]


def verify_source():
    env=previous.four.previous.fixed_environment(SYM);baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(primitives)==67 and counts=={'+':29,'*':38}
    assert len(OUTER)==24 and CORE==previous.CORE
    assert len(NAMES)==len(set(NAMES))==27 and len(sources)==len(EQUALITIES)==17
    penv={**SYM,**{name:sp.Symbol(name) for name in ('CE','W','Tend','Lend','betaend')}}
    baseline.run_schedule(PIN,penv);pinops,pincounts=verify_primitives(PIN,penv)
    assert len(pinops)==4 and pincounts=={'+':2,'*':2}
    assert sp.expand(penv['endpoint_rhs']-(penv['Lend']+penv['CE']*penv['W']*penv['Tend']))==0
    assert sp.expand(penv['endpoint_remainder_bound']-penv['Lend']-penv['betaend'])==0
    return dict(operations=67,multiplications=38,additions_subtractions=29,positive_unknown_count=27,
                equations=17,positive_unknowns=NAMES,parameters=[],primitive_instructions=primitives,
                sources=records,kernel_operations=43,kernel_source_identical=True,
                low_packed_field='B*Tmarker=C-2; same existing marker product reused',
                endpoint_pin={'operations':4,'multiplications':2,'additions':2,'extra_equations':2,
                              'extra_positive_unknowns':['Lend','betaend','Tend'],
                              'interface_coordinate':'W','primitive_instructions':pinops,
                              'preliminary_bound':'W<C<q follows before any power decoding',
                              'decoding_precondition':'W=B^j,1<=j<N; independently established'})


@dataclass(frozen=True)
class Compiled:
    k:int
    A:int
    clauses:tuple
    c:tuple
    mu:int
    m:int
    padding:int
    R:int
    B:int
    d:int
    Ds:tuple
    MC:int
    MF:int

    def cell(self,bits):
        assert len(bits)==self.m+1 and all(bit in (0,1) for bit in bits)
        return 2*sum(bit*self.R**j for j,bit in enumerate(bits))


def compile_rule(k,allowed):
    assert k>=2
    old=previous.compile_rule(k,allowed)
    target=max(2*(old.m+1)*sum(old.c),2*old.mu)+2
    R=1<<((target-1).bit_length());B=R**(k+old.m);d=B.bit_length()-1
    Ds=tuple(sum(old.c[s*k+i]*R**(k-1-i) for i in range(k)) for s in range(3))
    MC=B-1-2*sum(R**j for j in range(1,old.m+1));MF=2*old.mu*R**(k-1)
    assert B>=16 and all(0<value<B for value in Ds)
    assert 0<MC<=B-2 and 0<MF<=B-2 and MC%2 and MF%2==0
    assert MC.bit_count()==d-old.m and MF.bit_count()==old.m
    assert MC&2==2
    return Compiled(k,old.A,old.clauses,old.c,old.mu,old.m,old.padding,R,B,d,Ds,MC,MF)


def check_scalar(cc,allowed,genuine,fill):
    rows=[row+(fill,)*(cc.m+1-cc.k) for row in genuine]
    cells=[cc.cell(row) for row in rows]
    field=sum(coef*cell for coef,cell in zip(cc.Ds,cells))
    polynomial=[0]*(cc.k+cc.m)
    for s,row in enumerate(rows):
        for i in range(cc.k):
            for j,bit in enumerate(row):polynomial[cc.k-1+j-i]+=2*cc.c[s*cc.k+i]*bit
    assert sum(polynomial)<=2*(cc.m+1)*sum(cc.c)<=cc.R-2
    assert field==sum(value*cc.R**i for i,value in enumerate(polynomial))
    phi=sum(coef*bit for coef,bit in zip(cc.c,sum(genuine,())))
    assert polynomial[cc.k-1]==2*phi
    assert 0<=field<=cc.B-2
    truth=previous.scalar_truth(cc,allowed,genuine)
    assert (field&cc.MF==0)==truth
    for row,cell in zip(rows,cells):
        assert (cell&cc.MC==0)==(row[0]==0)
    return truth


def examples():
    return [(name,k,allowed) for name,k,allowed in previous.examples() if k>=2]


def verify_scalar():
    cases=0;records=[]
    for name,k,allowed in examples():
        cc=compile_rule(k,allowed);domain=tuple(product((0,1),repeat=k));accepted=0
        for rows in product(domain,repeat=3):
            for fill in (0,1):accepted+=check_scalar(cc,allowed,rows,fill);cases+=1
        records.append(dict(name=name,k=k,mask_bits=cc.m,cell_positions=cc.m+1,
                            cell_bits=cc.d,accepted=accepted))
    cc=compile_rule(32,None)
    assert cc.m==32 and cc.padding==12
    for bits in ((0,)*32,(1,)+(0,)*31,(0,)*31+(1,),(1,)*32):check_scalar(cc,None,(bits,)*3,1)
    return dict(cases=cases,examples=records,padding_cases=4,padded_zero_expression_clauses=cc.padding,
                extra_dummy_position_checked=True)


def numeric_outer(values,cc):
    const=dict(zip(('DC','DR','DY'),cc.Ds),B=cc.B,MC=cc.MC,MF=cc.MF)
    env=previous.four.previous.fixed_environment({**const,**values})
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left;bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def check_pin(cc,cells,C,q):
    CE=2*cc.R**(cc.k-1);assert cc.B%CE==0
    accepted=rejected=0
    for j in range(1,len(cells)):
        W=cc.B**j;Q,L=divmod(C,W)
        # Independent extraction of the genuine highest indicator.
        is_end=(cells[j]//(2*cc.R**(cc.k-1)))%cc.R==1
        assert (Q%CE==0)==is_end
        if is_end:
            Tend=Q//CE;beta=W-L
            assert min(L,beta,Tend)>0 and C==L+CE*W*Tend and L+beta==W
            assert W<C<q
            env=dict(CE=CE,W=W,Tend=Tend,Lend=L,betaend=beta)
            baseline.run_schedule(PIN,env)
            assert env['endpoint_rhs']==C and env['endpoint_remainder_bound']==W
            accepted+=1
        else:rejected+=1
    return accepted,rejected


def check_word(cc,allowed,genuine,hh,mode):
    N=len(genuine);B=cc.B
    rows=[row+(int(mode==1 or (mode==2 and i!=0)),)*(cc.m+1-cc.k) for i,row in enumerate(genuine)]
    cells=[cc.cell(row) for row in rows];q=B**N;P=B**hh;D=q-1;J=D//(B-1)
    pack=lambda values:sum(value*B**i for i,value in enumerate(values))
    C=pack(cells);RR=pack([cells[(i-hh)%N] for i in range(N)]);YY=pack([cells[(i-hh-1)%N] for i in range(N)])
    DC,DR,DY=cc.Ds;F=DC*C+DR*RR+DY*YY
    positions=lambda i:(i,(i-hh)%N,(i-hh-1)%N)
    local=all(previous.scalar_truth(cc,allowed,tuple(genuine[pos] for pos in positions(i))) for i in range(N))
    assert (F&(cc.MF*J)==0)==local
    marker=cells[0]==2
    genuine_valid=all(sum(row)==1 for row in genuine)
    unique=marker and sum(row[0] for row in genuine)==1
    original=(N>=2 and genuine_valid and unique and
              all(previous.four.permitted(allowed,[genuine[pos].index(1) for pos in positions(i)]) for i in range(N)))
    result=dict(accepted=False,marker_rejected=not marker,positive_tail_rejected=False,
                duplicate_start_rejected=False,pin_accepts=0,pin_rejects=0)
    if not marker:
        assert not original;return result
    Z=C-2;T,rem=divmod(Z,B);assert rem==0
    if T<=0:
        assert Z==0 and not original;result['positive_tail_rejected']=True;return result
    assert N>=2 and 0<Z<C<q and 0<F<D
    low_ok=Z&(cc.MC*J)==0
    assert low_ok==all(row[0]==0 for row in genuine[1:])
    assert (low_ok and local)==original
    L=q*q;S=Z+q*F;M=(cc.MC+q*cc.MF)*J;r=(L-S)*(L-1)+M
    assert 0<S<L and 0<M<L-1 and q*q<=r<q**4 and r%2==1
    assert M.bit_count()==cc.d*N and (r.bit_count()==3*cc.d*N)==(S&M==0)==original
    K=DC+(DR+B*DY)*P;z,rem=divmod(K*C-F,D);assert rem==0
    kR=(P*C-RR)//D;kY=(B*P*C-YY)//D
    assert kR>=0 and kY>=0 and z==DR*kR+DY*kY
    if original:
        assert C>=2*J and kY>=2*P and z>=2*DY*P>0
        values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=(P-1)//(B-1),F=F,
                    alpha=q-C,zquot=z,r=r,Tmarker=T)
        env=numeric_outer(values,cc)
        assert min(values.values())>0 and all(env[a]==env[b] for a,b in OUTER_EQUALITIES)
        result['accepted']=True
        result['pin_accepts'],result['pin_rejects']=check_pin(cc,cells,C,q)
    if local and not low_ok:result['duplicate_start_rejected']=True
    return result


def verify_cyclic():
    keys=('accepted','marker_rejected','positive_tail_rejected','duplicate_start_rejected','pin_accepts','pin_rejects')
    total=dict.fromkeys(keys,0);cases=0;records=[]
    for name,k,allowed in examples():
        cc=compile_rule(k,allowed);domain=tuple(product((0,1),repeat=k));count=accepted=0
        for N in range(1,(2 if k==3 else 3)+1):
            for word in product(domain,repeat=N):
                for hh in range(1,N+1):
                    for mode in range(3):
                        result=check_word(cc,allowed,word,hh,mode)
                        cases+=1;count+=1;accepted+=result['accepted']
                        for key in keys:total[key]+=result[key]
        records.append(dict(name=name,cyclic_cases=count,accepted=accepted))
    cc=compile_rule(2,None)
    assert check_word(cc,None,((1,0),),1,0)['positive_tail_rejected']
    assert check_word(cc,None,((1,0),(1,0)),1,0)['duplicate_start_rejected']
    copy=next(allowed for name,k,allowed in examples() if name=='binary_copy_center')
    cc=compile_rule(2,copy);word=((1,0),(0,1))
    for mode in (0,2):
        assert check_word(cc,copy,word,1,mode)['accepted']
        assert not check_word(cc,copy,word,2,mode)['accepted']
    assert all(total[key]>0 for key in keys)
    return dict(cases=cases,**total,examples=records,directional_extra_cases=4,
                length_one_rejected_and_repetition_duplicates_start=True,
                arbitrary_dummy_bits_above_End_checked=True,full_packed_Pell_tuples_materialized=False)


def verify():
    return dict(status='PASS_UNIQUE_START_CYCLIC67',source=verify_source(),scalar=verify_scalar(),cyclic=verify_cyclic(),
                proof='../1980/EXPLORATION_UNIQUE_START_CYCLIC_67.md',complete_raw_input_universal_certificate=False,
                scope='Complete67-operation unique-Start cyclic predicate for N>=2, plus conditional four-operation highest-genuine-state endpoint pin')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',result['cyclic']['cases'],'cyclic cases')
