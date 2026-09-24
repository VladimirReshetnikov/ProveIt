#!/usr/bin/env python3
"""Homogeneous one-hot compiler and complete marked70 source.

Fixed machine/input tables become free numerals. This is not a fixed-index
raw-input universal certificate. No full enormous Pell tuple is generated.
"""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

import explore_multibit_cyclic_certificate as previous
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NAMES=previous.NAMES+['Tmarker']
CONSTANTS=[name for name in previous.CONSTANT_NAMES if name!='G0']
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANTS}
OUTER=[row for row in previous.OUTER if row[0] not in ('GJ','local_lhs')]
OUTER += [('Bmarker_tail','*','B','Tmarker'),('marked_rhs','+',2,'Bmarker_tail')]
CORE=list(previous.CORE)
SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('local_sum',right) if left=='local_lhs' else (left,right)
                  for left,right in previous.OUTER_EQUALITIES]+[('C','marked_rhs')]
EQUALITIES=OUTER_EQUALITIES+previous.retained.previous.retained.retained.CORE_EQUALITIES


def verify_source():
    env=previous.fixed_environment(SYM)
    histogram=baseline.run_schedule(SCHEDULE,env)
    old=[expr.subs(previous.SYM['G0'],0) for expr in previous.source_residuals()]
    sources=old[:6]+[SYM['C']-2-SYM['B']*SYM['Tmarker']]+old[6:]
    u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if index==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==27 and len(CORE)==43 and len(primitives)==70
    assert counts=={'+':30,'*':40}
    assert len(NAMES)==len(set(NAMES))==27 and len(EQUALITIES)==len(sources)==17
    assert CORE==previous.retained.CORE
    return dict(operations=70,multiplications=40,additions_subtractions=30,
                positive_unknown_count=27,positive_unknowns=NAMES,parameters=[],equations=17,
                fixed_constants=CONSTANTS,primitive_instructions=primitives,histogram=histogram,
                sources=records,kernel_operations=43,kernel_source_identical=True,
                prior_kernel_evidence='explore_multibit_cyclic_certificate.json: pell',
                ledger={'geometry':5,'bound':1,'homogeneous_transport':8,'packing':11,'marker':2})


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
        assert len(bits)==self.m and all(b in (0,1) for b in bits)
        return 2*sum(b*self.R**j for j,b in enumerate(bits))

    def constants(self):
        return dict(zip(('DL','DC','DR','DY'),self.Ds),B=self.B,MC=self.MC,MF=self.MF)


def compile_rule(k,allowed):
    assert k>=1
    if allowed is not None:
        assert all(len(row)==4 and all(0<=a<k for a in row) for row in allowed)
    A=8
    while A<=max(2*k,4):A*=2
    clauses=[]
    def clause(indices,mask):
        weights=[0]*(4*k)
        for index in indices:weights[index]+=1
        clauses.append((tuple(weights),mask))
    for s in range(4):clause(range(s*k,(s+1)*k),A-2)
    for neighbor in (0,3):clause(list(range(k,2*k))+list(range(neighbor*k,(neighbor+1)*k)),1)
    if allowed is not None:
        for row in product(range(k),repeat=4):
            if row not in allowed:clause([s*k+a for s,a in enumerate(row)],4)
    m=sum(mask.bit_count() for _,mask in clauses);padding=max(0,k-m)
    for _ in range(padding):clause((),1)
    m+=padding
    c=tuple(sum(weights[i]*A**j for j,(weights,_) in enumerate(clauses)) for i in range(4*k))
    mu=sum(mask*A**j for j,(_,mask) in enumerate(clauses))
    assert min(c)>0 and mu.bit_count()==m>=k
    mass=2*m*sum(c);target=max(mass,2*mu)+2
    R=1<<((target-1).bit_length());B=R**(k+m-1);d=B.bit_length()-1
    Ds=tuple(sum(c[s*k+i]*R**(k-1-i) for i in range(k)) for s in range(4))
    MC=B-1-2*sum(R**j for j in range(m));MF=2*mu*R**(k-1)
    assert B>=16 and all(0<v<B for v in Ds)
    assert 0<MC<=B-2 and 0<MF<=B-2 and MC%2==1 and MF%2==0
    assert MC.bit_count()==d-m and MF.bit_count()==m
    return Compiled(k,A,tuple(clauses),c,mu,m,padding,R,B,d,Ds,MC,MF)


def permitted(allowed,states):
    return allowed is None or tuple(states) in allowed


def scalar_truth(cc,allowed,genuine):
    occupancy=[sum(row) for row in genuine]
    if any(n>1 for n in occupancy):return False
    if occupancy[1]!=occupancy[0] or occupancy[1]!=occupancy[3]:return False
    if all(occupancy):
        return permitted(allowed,[row.index(1) for row in genuine])
    return True


def check_scalar(cc,allowed,genuine,fill):
    flat=sum(genuine,());rows=[row+(fill,)*(cc.m-cc.k) for row in genuine]
    digits=[sum(w*b for w,b in zip(weights,flat)) for weights,_ in cc.clauses]
    assert all(0<=digit<cc.A for digit in digits)
    phi=sum(c*b for c,b in zip(cc.c,flat))
    assert phi==sum(value*cc.A**j for j,value in enumerate(digits))
    expected=scalar_truth(cc,allowed,genuine)
    assert (phi&cc.mu==0)==expected
    cells=[cc.cell(row) for row in rows]
    field=sum(d*c for d,c in zip(cc.Ds,cells))
    polynomial=[0]*(cc.k+cc.m-1)
    for s,row in enumerate(rows):
        for i in range(cc.k):
            for j,bit in enumerate(row):
                polynomial[cc.k-1+j-i]+=2*cc.c[s*cc.k+i]*bit
    assert sum(polynomial)<=2*cc.m*sum(cc.c)<=cc.R-2
    assert field==sum(value*cc.R**j for j,value in enumerate(polynomial))
    assert field//cc.R**(cc.k-1)%cc.R==2*phi
    assert 0<=field<=cc.B-2 and (field&cc.MF==0)==expected
    assert all(value&cc.MC==0 and value%2==0 and 0<=value<cc.B for value in cells)
    return expected


def examples():
    rule110=frozenset((l,c,r,(110>>(4*l+2*c+r))&1) for l,c,r in product(range(2),repeat=3))
    copy2=frozenset((l,c,r,l) for l,c,r in product(range(2),repeat=3))
    return [('singleton_full',1,None),('singleton_empty',1,frozenset()),
            ('binary_full',2,None),('binary_empty',2,frozenset()),
            ('binary_rule110',2,rule110),('binary_copy_left',2,copy2),
            ('ternary_full',3,None)]


def verify_scalar():
    cases=0;records=[]
    for name,k,allowed in examples():
        cc=compile_rule(k,allowed);accepted=0
        domain=tuple(product((0,1),repeat=k))
        for genuine in product(domain,repeat=4):
            for fill in (0,1):
                accepted+=check_scalar(cc,allowed,genuine,fill);cases+=1
        records.append(dict(name=name,k=k,clauses=len(cc.clauses),mask_bits=cc.m,
                            cell_bits=cc.d,accepted_scalar_cases=accepted))
    # Clause count and mask population differ, and padding is independently exercised.
    cc=compile_rule(32,None)
    assert cc.padding==6 and cc.m==32
    padding_cases=0
    for bits in ((0,)*32,(1,)+(0,)*31,(1,1)+(0,)*30,(1,)*32):
        check_scalar(cc,None,(bits,)*4,0);padding_cases+=1
    return dict(cases=cases,examples=records,padding_cases=padding_cases,
                padded_alphabet_size=32,padded_zero_expression_clauses=cc.padding)


def numeric_outer(values,const):
    env=previous.fixed_environment({**const,**values})
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left;bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def check_word(cc,allowed,genuine,hh,mode):
    N=len(genuine);B=cc.B
    rows=[row+(int(mode==1 or (mode==2 and i!=0)),)*(cc.m-cc.k) for i,row in enumerate(genuine)]
    cells=[cc.cell(row) for row in rows]
    q=B**N;P=B**hh;D=q-1;J=D//(B-1)
    pack=lambda values:sum(value*B**i for i,value in enumerate(values))
    C=pack(cells)
    left=pack([cells[(i+hh)%N] for i in range(N)])
    right=pack([cells[(i-hh)%N] for i in range(N)])
    nxt=pack([cells[(i-hh-1)%N] for i in range(N)])
    F=sum(coef*word for coef,word in zip(cc.Ds,(left,C,right,nxt)))
    local=all(scalar_truth(cc,allowed,tuple(genuine[pos] for pos in ((i+hh)%N,i,(i-hh)%N,(i-hh-1)%N)))
              for i in range(N))
    assert (F&(cc.MF*J)==0)==local
    true_states=all(sum(row)==1 for row in genuine)
    marker=cells[0]==2
    original=(true_states and marker and all(permitted(allowed,
              [genuine[pos].index(1) for pos in ((i+hh)%N,i,(i-hh)%N,(i-hh-1)%N)]) for i in range(N)))
    assert (local and marker)==original
    if C==0:
        assert F==0 and not marker
        return dict(positive=False,marked=False,local=local,dummy_only=False)
    assert 0<F<D and C&(cc.MC*J)==0
    L=q*q;S=C+q*F;M=(cc.MC+q*cc.MF)*J;r=(L-S)*(L-1)+M
    assert 0<S<L and 0<M<L-1 and q*q<=r<q**4 and r%2==1
    assert M.bit_count()==cc.d*N
    assert (r.bit_count()==3*cc.d*N)==(S&M==0)==local
    DL,DC,DR,DY=cc.Ds
    K=DL+P*(DC+(DR+B*DY)*P)
    z,remainder=divmod(K*C-P*F,D);assert remainder==0
    kL=(P*left-C)//D;kR=(P*C-right)//D;kY=(B*P*C-nxt)//D
    assert 0<=kL<P and kR>=0 and kY>=0
    assert z==P*(DR*kR+DY*kY)-DL*kL
    if original:
        assert min(cells)>=2 and kY>=2*P and z>2*P*P-B*(P-1)>0
        if N>=2:
            T,rem=divmod(C-2,B);assert rem==0 and T>0
            values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=(P-1)//(B-1),F=F,
                        alpha=q-C,zquot=z,r=r,Tmarker=T)
            env=numeric_outer(values,cc.constants())
            assert min(values.values())>0
            assert all(env[a]==env[b] for a,b in OUTER_EQUALITIES)
    return dict(positive=True,marked=bool(original),local=local,
                dummy_only=not any(any(row) for row in genuine))


def verify_cyclic():
    cases=marked=positive_marked=empty_projected=locally_valid_unmarked=0;records=[]
    for name,k,allowed in examples():
        cc=compile_rule(k,allowed);domain=tuple(product((0,1),repeat=k));count=accepted=0
        maximum=2 if k==3 else 3
        for N in range(1,maximum+1):
            for word in product(domain,repeat=N):
                for hh in range(1,N+1):
                    for mode in range(3):
                        result=check_word(cc,allowed,word,hh,mode)
                        cases+=1;count+=1;marked+=result['marked'];accepted+=result['marked']
                        positive_marked+=result['marked'] and N>=2
                        empty_projected+=result['dummy_only']
                        locally_valid_unmarked+=result['positive'] and result['local'] and not result['marked']
        records.append(dict(name=name,cyclic_cases=count,marked_cases=accepted,maximum_length=maximum))
    # Genuine marker at length1 is repeated, giving a positive tail.
    cc=compile_rule(1,None)
    assert check_word(cc,None,((1,),),1,0)['marked']
    assert check_word(cc,None,((1,),(1,)),1,0)['marked']
    assert empty_projected>0 and locally_valid_unmarked>0 and positive_marked>0
    return dict(cases=cases,marked_cases=marked,positive_marked_outer_tuples=positive_marked,
                positive_dummy_only_words=empty_projected,
                locally_valid_positive_unmarked_words=locally_valid_unmarked,
                length_one_repeat_checked=True,examples=records,full_packed_Pell_tuples_materialized=False)


def verify():
    return dict(status='PASS_HOMOGENEOUS_MARKED70',source=verify_source(),
                scalar=verify_scalar(),cyclic=verify_cyclic(),
                proof='../1980/EXPLORATION_HOMOGENEOUS_MARKED_CYCLIC_70.md',
                fixed_index_raw_input_improvement=False,
                scope='Complete positive marked cyclic existence and effective halting-instance compilation; machine and input are both encoded in fixed numerals')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',result['scalar']['cases'],
          'scalar cases;',result['cyclic']['cases'],'cyclic cases')
