#!/usr/bin/env python3
"""Complete marked three-cell67; fixed numerals encode machine and input."""
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

import explore_homogeneous_marked_cyclic as four
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NAMES=list(four.NAMES)
CONSTANTS=[name for name in four.CONSTANTS if name!='DL']
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANTS}
OUTER=[]
for row in four.OUTER:
    if row[0] in ('transport_gap','Pgap','DLC','local_sum'):continue
    OUTER.append(row)
    if row[0]=='local_rhs':OUTER.append(('local_rhs_sum','+','F','local_rhs'))
CORE=list(four.CORE);SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('innerC','local_rhs_sum') if left=='local_sum' else (left,right)
                  for left,right in four.OUTER_EQUALITIES]
EQUALITIES=OUTER_EQUALITIES+four.previous.retained.previous.retained.retained.CORE_EQUALITIES


def verify_source():
    env=four.previous.fixed_environment(SYM);histogram=baseline.run_schedule(SCHEDULE,env)
    z=SYM;q,P,C,F,J=[z[name] for name in ('q','P','C','F','Jrep')]
    old=four.previous.source_residuals()
    sources=[(z['B']-1)*J-q+1,P*z['v']-q,(z['B']-1)*z['align']-P+1,C+z['alpha']-q,
             (z['DC']+(z['DR']+z['B']*z['DY'])*P)*C-F-z['zquot']*(q-1),
             z['r']-(q*q-C-q*F)*(q*q-1)-(z['MC']+q*z['MF'])*J,
             C-2-z['B']*z['Tmarker']]+old[6:]
    u=z['j']*z['c']-(2*z['r']+1);correction=sources[14]*(u*u-z['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if index==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==24 and len(CORE)==43 and len(primitives)==67
    assert counts=={'+':29,'*':38} and len(sources)==len(EQUALITIES)==17
    assert len(NAMES)==len(set(NAMES))==27 and CORE==four.CORE
    return dict(operations=67,multiplications=38,additions_subtractions=29,positive_unknown_count=27,
                positive_unknowns=NAMES,parameters=[],equations=17,fixed_constants=CONSTANTS,
                primitive_instructions=primitives,histogram=histogram,sources=records,
                kernel_operations=43,kernel_source_identical=True,
                ledger={'geometry':5,'bound':1,'local':5,'packing':11,'marker':2})


def compile_rule(k,allowed):
    A=8
    while A<=max(2*k,4):A*=2
    clauses=[]
    def clause(terms,mask):
        weights=[0]*(3*k)
        for index,weight in terms:weights[index]+=weight
        clauses.append((tuple(weights),mask))
    for s in range(3):clause([(s*k+i,1) for i in range(k)],A-2)
    for s in (1,2):clause([(i,1) for i in range(k)]+[(s*k+i,1) for i in range(k)],1)
    if allowed is not None:
        assert all(len(row)==3 and all(0<=a<k for a in row) for row in allowed)
        for row in product(range(k),repeat=3):
            if row not in allowed:clause([(s*k+a,1 if s<2 else 2) for s,a in enumerate(row)],4)
    m=sum(mask.bit_count() for _,mask in clauses);padding=max(0,k-m)
    for _ in range(padding):clause((),1)
    m+=padding
    c=tuple(sum(weights[i]*A**j for j,(weights,_) in enumerate(clauses)) for i in range(3*k))
    mu=sum(mask*A**j for j,(_,mask) in enumerate(clauses));assert mu.bit_count()==m>=k and min(c)>0
    target=max(2*m*sum(c),2*mu)+2;R=1<<((target-1).bit_length())
    B=R**(k+m-1);d=B.bit_length()-1
    Ds=tuple(sum(c[s*k+i]*R**(k-1-i) for i in range(k)) for s in range(3))
    MC=B-1-2*sum(R**j for j in range(m));MF=2*mu*R**(k-1)
    assert B>=16 and all(0<v<B for v in Ds)
    assert 0<MC<=B-2 and 0<MF<=B-2 and MC%2 and MF%2==0
    assert MC.bit_count()==d-m and MF.bit_count()==m
    return four.Compiled(k,A,tuple(clauses),c,mu,m,padding,R,B,d,Ds,MC,MF)


def scalar_truth(cc,allowed,genuine):
    occupancy=[sum(row) for row in genuine]
    if any(n>1 for n in occupancy) or len(set(occupancy))!=1:return False
    return not all(occupancy) or four.permitted(allowed,[row.index(1) for row in genuine])


def check_scalar(cc,allowed,genuine,fill):
    flat=sum(genuine,());rows=[row+(fill,)*(cc.m-cc.k) for row in genuine]
    digits=[sum(w*b for w,b in zip(weights,flat)) for weights,_ in cc.clauses]
    assert all(0<=digit<cc.A for digit in digits)
    phi=sum(c*b for c,b in zip(cc.c,flat))
    assert phi==sum(value*cc.A**j for j,value in enumerate(digits))
    expected=scalar_truth(cc,allowed,genuine);assert (phi&cc.mu==0)==expected
    cells=[cc.cell(row) for row in rows];field=sum(d*c for d,c in zip(cc.Ds,cells))
    polynomial=[0]*(cc.k+cc.m-1)
    for s,row in enumerate(rows):
        for i in range(cc.k):
            for j,bit in enumerate(row):polynomial[cc.k-1+j-i]+=2*cc.c[s*cc.k+i]*bit
    assert sum(polynomial)<=2*cc.m*sum(cc.c)<=cc.R-2
    assert field==sum(value*cc.R**j for j,value in enumerate(polynomial))
    assert field//cc.R**(cc.k-1)%cc.R==2*phi
    assert 0<=field<=cc.B-2 and (field&cc.MF==0)==expected
    return expected


def examples():
    copy=frozenset((c,r,c) for c,r in product(range(2),repeat=2))
    xor=frozenset((c,r,c^r) for c,r in product(range(2),repeat=2))
    return [('singleton_full',1,None),('singleton_empty',1,frozenset()),
            ('binary_full',2,None),('binary_empty',2,frozenset()),
            ('binary_copy_center',2,copy),('binary_xor',2,xor),('ternary_full',3,None)]


def verify_scalar():
    cases=0;records=[]
    for name,k,allowed in examples():
        cc=compile_rule(k,allowed);accepted=0;domain=tuple(product((0,1),repeat=k))
        for genuine in product(domain,repeat=3):
            for fill in (0,1):accepted+=check_scalar(cc,allowed,genuine,fill);cases+=1
        records.append(dict(name=name,k=k,clauses=len(cc.clauses),mask_bits=cc.m,
                            cell_bits=cc.d,accepted_cases=accepted))
    cc=compile_rule(32,None);assert cc.padding==12 and cc.m==32
    for bits in ((0,)*32,(1,)+(0,)*31,(1,1)+(0,)*30,(1,)*32):check_scalar(cc,None,(bits,)*3,0)
    return dict(cases=cases,examples=records,padding_cases=4,padded_zero_expression_clauses=cc.padding)


def numeric_outer(values,cc):
    const=dict(zip(('DC','DR','DY'),cc.Ds),B=cc.B,MC=cc.MC,MF=cc.MF)
    env=four.previous.fixed_environment({**const,**values})
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left;bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def check_word(cc,allowed,genuine,hh,mode):
    N=len(genuine);B=cc.B
    rows=[row+(int(mode==1 or (mode==2 and i!=0)),)*(cc.m-cc.k) for i,row in enumerate(genuine)]
    cells=[cc.cell(row) for row in rows];q=B**N;P=B**hh;D=q-1;J=D//(B-1)
    pack=lambda values:sum(value*B**i for i,value in enumerate(values))
    C=pack(cells);RR=pack([cells[(i-hh)%N] for i in range(N)]);YY=pack([cells[(i-hh-1)%N] for i in range(N)])
    DC,DR,DY=cc.Ds;F=DC*C+DR*RR+DY*YY
    positions=lambda i:(i,(i-hh)%N,(i-hh-1)%N)
    local=all(scalar_truth(cc,allowed,tuple(genuine[pos] for pos in positions(i))) for i in range(N))
    assert (F&(cc.MF*J)==0)==local
    marker=cells[0]==2
    original=(all(sum(row)==1 for row in genuine) and marker and
              all(four.permitted(allowed,[genuine[pos].index(1) for pos in positions(i)]) for i in range(N)))
    assert (local and marker)==original
    if not C:
        assert F==0 and not marker
        return dict(marked=False,positive_marked=False,dummy_only=False,unmarked=False)
    assert 0<F<D and 0<C<q and C&(cc.MC*J)==0
    L=q*q;S=C+q*F;M=(cc.MC+q*cc.MF)*J;r=(L-S)*(L-1)+M
    assert 0<S<L and 0<M<L-1 and q*q<=r<q**4 and r%2==1
    assert M.bit_count()==cc.d*N and (r.bit_count()==3*cc.d*N)==(S&M==0)==local
    K=DC+(DR+B*DY)*P;z,rem=divmod(K*C-F,D);assert rem==0
    kR=(P*C-RR)//D;kY=(B*P*C-YY)//D
    assert kR>=0 and kY>=0 and z==DR*kR+DY*kY
    if original:
        assert min(cells)>=2 and C>=2*J and kY>=2*P and z>=2*DY*P>0
        if N>=2:
            T,rem=divmod(C-2,B);assert rem==0 and T>0
            values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=(P-1)//(B-1),F=F,
                        alpha=q-C,zquot=z,r=r,Tmarker=T)
            env=numeric_outer(values,cc)
            assert min(values.values())>0 and all(env[a]==env[b] for a,b in OUTER_EQUALITIES)
    return dict(marked=bool(original),positive_marked=bool(original and N>=2),
                dummy_only=not any(any(row) for row in genuine),unmarked=bool(local and not marker))


def verify_cyclic():
    cases=marked=positive_marked=dummy_only=unmarked=0;records=[]
    for name,k,allowed in examples():
        cc=compile_rule(k,allowed);domain=tuple(product((0,1),repeat=k));count=accepted=0
        for N in range(1,(2 if k==3 else 3)+1):
            for word in product(domain,repeat=N):
                for hh in range(1,N+1):
                    for mode in range(3):
                        result=check_word(cc,allowed,word,hh,mode)
                        cases+=1;count+=1;marked+=result['marked'];accepted+=result['marked']
                        positive_marked+=result['positive_marked'];dummy_only+=result['dummy_only'];unmarked+=result['unmarked']
        records.append(dict(name=name,cyclic_cases=count,marked_cases=accepted))
    cc=compile_rule(1,None)
    assert check_word(cc,None,((1,),),1,0)['marked']
    assert check_word(cc,None,((1,),(1,)),1,0)['positive_marked']
    copy=examples()[4][2];cc=compile_rule(2,copy);word=((1,0),(0,1))
    for mode in (0,2):
        assert check_word(cc,copy,word,1,mode)['positive_marked']
        assert not check_word(cc,copy,word,2,mode)['marked']
    assert positive_marked>0 and dummy_only>0 and unmarked>0
    return dict(cases=cases,marked_cases=marked,positive_marked_outer_tuples=positive_marked,
                positive_dummy_only_words=dummy_only,locally_valid_unmarked_words=unmarked,
                directional_extra_cases=4,length_one_repeat_checked=True,examples=records,
                full_packed_Pell_tuples_materialized=False)


def verify():
    return dict(status='PASS_THREE_CELL_MARKED67',source=verify_source(),scalar=verify_scalar(),cyclic=verify_cyclic(),
                proof='../1980/EXPLORATION_THREE_CELL_MARKED_67.md',fixed_index_raw_input_improvement=False,
                scope='Complete positive marked three-cell cyclic existence; exact-period block lift supplies compiled halting instances, with machine and input in fixed numerals')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',result['scalar']['cases'],
          'scalar cases;',result['cyclic']['cases'],'cyclic cases')
