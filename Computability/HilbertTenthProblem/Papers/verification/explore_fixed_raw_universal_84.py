#!/usr/bin/env python3
"""Complete84 raw universal source: unshifted bits and two direct markers."""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

import explore_unique_start_cyclic as unique
import explore_raw_input_exponent_bridge as exponent
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NAMES=[name if name!='Tmarker' else 'Z' for name in unique.NAMES]+exponent.NEW_NAMES
CONSTANTS=unique.CONSTANTS+['CS']
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANTS+['x']}
OUTER=[]
for row in unique.OUTER:
    if row[0] in ('Bmarker_tail','marked_rhs'):continue
    if row[0]=='qF':
        OUTER.extend([('marker_partial','+','CS','Z'),('marked_rhs','+','marker_partial','W')])
    if row[0]=='packed':row=('packed','+','Z','qF')
    OUTER.append(row)
CORE=list(unique.CORE)
ADAPTER=[(name,op,left,2 if right=='c0' else right) for name,op,left,right in exponent.ADAPTER]
SCHEDULE=OUTER+CORE+ADAPTER
OUTER_EQUALITIES=list(unique.OUTER_EQUALITIES)
EQUALITIES=[('raw_bound','q') if pair==('bounded','q') else pair for pair in unique.EQUALITIES]+[
    ('kappa','index_rhs'),('c','pell_gap'),('mu2','norm_rhs'),('mu','exponent_rhs')]


def source_residuals():
    z=SYM;q,P,C,F,J=[z[name] for name in ('q','P','C','F','Jrep')]
    sources=[(z['B']-1)*J-q+1,P*z['v']-q,(z['B']-1)*z['align']-P+1,C+z['alpha']+z['x']+2-q,
             (z['DC']+(z['DR']+z['B']*z['DY'])*P)*C-F-z['zquot']*(q-1),
             z['r']-(q*q-z['Z']-q*F)*(q*q-1)-(z['MC']+q*z['MF'])*J,
             C-z['CS']-z['Z']-z['W']]+unique.source_residuals()[7:]
    A0=z['a']+2;D=A0*A0-1;t=z['x']+2
    return sources+[z['kappa']-t-z['delta']*(z['a']+1),z['c']-z['kappa']-z['phi'],
                    z['mu']**2-1-D*z['kappa']**2,
                    z['mu']-z['W']-z['kappa']*(A0-P)-z['rho']*(D-(A0-P)**2)]


def verify_source():
    env=unique.previous.four.previous.fixed_environment(SYM);baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==24 and len(CORE)==43 and len(ADAPTER)==17
    assert len(primitives)==84 and counts=={'+':40,'*':44}
    assert len(NAMES)==len(set(NAMES))==33 and len(sources)==len(EQUALITIES)==21
    assert CORE==unique.CORE and not any('Tmarker'==operand for row in SCHEDULE for operand in row)
    assert sp.expand(env['packed']-SYM['Z']-SYM['q']*SYM['F'])==0
    assert sp.expand(env['marked_rhs']-SYM['CS']-SYM['Z']-SYM['W'])==0
    assert sp.expand(env['raw_t']-SYM['x']-2)==0
    used=set().union(*(expr.free_symbols for expr in sources))
    assert {SYM[name] for name in NAMES}<=used
    initial=unique.previous.four.previous.fixed_environment(SYM)
    aliases={name:value for name,value in initial.items() if name not in SYM}
    assert all(sp.sympify(value).free_symbols<={SYM[name] for name in CONSTANTS} for value in aliases.values())
    return dict(operations=84,multiplications=44,additions_subtractions=40,
                positive_existential_unknown_count=33,positive_unknowns=NAMES,raw_parameters=['x>0'],
                equations=21,fixed_constants=CONSTANTS,fixed_aliases={name:sp.sstr(v) for name,v in aliases.items()},
                primitive_instructions=primitives,sources=records,kernel_source_identical=True,
                ledger={'geometry':5,'existing_bound_register':1,'transport':5,'packing':11,
                        'two_marker_additions':2,'kernel':43,'raw_exponent_and_strengthened_bound':17},
                complete_fixed_index_raw_input_universal_certificate=True)


@dataclass(frozen=True)
class Compiled(unique.Compiled):
    def cell(self,bits):
        assert len(bits)==self.m+2 and all(bit in (0,1) for bit in bits)
        return sum(bit*self.R**j for j,bit in enumerate(bits))


def compile_rule(k,allowed):
    assert k>=2
    old=unique.previous.compile_rule(k,allowed)
    target=max((old.m+2)*sum(old.c),old.mu)+2
    R=1<<((target-1).bit_length());B=R**(k+old.m+1);d=B.bit_length()-1
    Ds=tuple(sum(old.c[s*k+i]*R**(k-1-i) for i in range(k)) for s in range(3))
    MC=B-1-sum(R**j for j in range(2,old.m+2));MF=old.mu*R**(k-1)
    assert B>=16 and all(0<value<B for value in Ds)
    assert 0<MC<=B-2 and 0<MF<=B-2 and MC%2 and MF%2==0
    assert MC.bit_count()==d-old.m and MF.bit_count()==old.m
    assert MC&1 and MC&R
    return Compiled(k,old.A,old.clauses,old.c,old.mu,old.m,old.padding,R,B,d,Ds,MC,MF)


def constants(cc):
    return dict(zip(('DC','DR','DY'),cc.Ds),B=cc.B,MC=cc.MC,MF=cc.MF,CS=cc.R)


def verify_scalar():
    cases=0;records=[]
    for name,k,allowed in unique.examples():
        cc=compile_rule(k,allowed);domain=tuple(product((0,1),repeat=k));accepted=0
        for genuine in product(domain,repeat=3):
            for fill in (0,1):
                rows=[row+(fill,)*(cc.m+2-k) for row in genuine]
                cells=[cc.cell(row) for row in rows]
                field=sum(coef*cell for coef,cell in zip(cc.Ds,cells))
                polynomial=[0]*(k+cc.m+1)
                for s,row in enumerate(rows):
                    for i in range(k):
                        for j,bit in enumerate(row):polynomial[k-1+j-i]+=cc.c[s*k+i]*bit
                assert sum(polynomial)<=(cc.m+2)*sum(cc.c)<=cc.R-2
                assert field==sum(value*cc.R**j for j,value in enumerate(polynomial))
                phi=sum(coef*bit for coef,bit in zip(cc.c,sum(genuine,())))
                assert polynomial[k-1]==phi and 0<=field<=cc.B-2
                expected=unique.previous.scalar_truth(cc,allowed,genuine)
                assert (field&cc.MF==0)==expected
                for row,cell in zip(rows,cells):
                    assert 0<=cell<=cc.B-2 and (cell&cc.MC==0)==(row[0]==row[1]==0)
                accepted+=expected;cases+=1
        records.append(dict(name=name,k=k,mask_bits=cc.m,cell_positions=cc.m+2,
                            cell_bits=cc.d,accepted=accepted))
    cc=compile_rule(32,None);assert cc.m==32 and cc.padding==12
    assert cc.MC.bit_count()+cc.MF.bit_count()==cc.d
    return dict(cases=cases,examples=records,padded_alphabet_size=32,
                padded_zero_expression_clauses=cc.padding,native_factor=1,End_code=1,Start_code='R')


def numeric_outer(values,cc):
    env=unique.previous.four.previous.fixed_environment({**constants(cc),**values})
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left;bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def actual_field(cc,cells,h):
    N=len(cells);B=cc.B
    pack=lambda values:sum(value*B**i for i,value in enumerate(values))
    C=pack(cells);right=pack([cells[(i-h)%N] for i in range(N)])
    nxt=pack([cells[(i-h-1)%N] for i in range(N)])
    F=sum(coef*value for coef,value in zip(cc.Ds,(C,right,nxt)))
    digits=[cc.Ds[0]*cells[i]+cc.Ds[1]*cells[(i-h)%N]+cc.Ds[2]*cells[(i-h-1)%N] for i in range(N)]
    assert all(0<=value<=B-2 for value in digits) and F==pack(digits)
    return C,right,nxt,F


def verify_composed_interfaces():
    full=None
    asymmetric=frozenset(row for row in product(range(3),repeat=3) if row!=(2,0,1))
    cases=nondivisible_Z=mutations=reverse_rejections=wrong_inputs=0
    max_q_bits=max_kappa_bits=0;records=[]
    for name,allowed in (('all ternary states',full),('forbid directional triple201',asymmetric)):
        cc=compile_rule(3,allowed);B,R=cc.B,cc.R
        for x in range(1,6):
            t=x+2
            for h in (1,2,3):
                for extra in (1,2):
                    N=h*t+extra;states=[1]+[2]*(N-1);states[h*t]=0
                    for mode in (0,1,2):
                        rows=[tuple(int(j==state) for j in range(3))+
                              tuple(0 if mode==0 else 1 if mode==1 else (i+j)%2
                                    for j in range(cc.m+2-3)) for i,state in enumerate(states)]
                        cells=[cc.cell(row) for row in rows]
                        C,RR,YY,F=actual_field(cc,cells,h)
                        q,P=B**N,B**h;W=P**t;Z=C-R-W;J,D=(q-1)//(B-1),q-1
                        assert 0<Z<C<q and 0<W<C<q and Z%2==0
                        assert C==R+Z+W and Z&(cc.MC*J)==0 and F&(cc.MF*J)==0
                        assert all(unique.previous.four.permitted(allowed,(states[i],states[(i-h)%N],states[(i-h-1)%N])) for i in range(N))
                        if Z%B:nondivisible_Z+=1
                        r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
                        assert r%2 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
                        kR=(P*C-RR)//D;kY=(B*P*C-YY)//D
                        zquot=cc.Ds[1]*kR+cc.Ds[2]*kY
                        assert C>=J and kR>=0 and kY>=P and zquot>=cc.Ds[2]*P>0
                        values=dict(q=q,P=P,C=C,Z=Z,v=q//P,Jrep=J,align=(P-1)//(B-1),
                                    F=F,alpha=q-C-t,zquot=zquot,r=r,W=W)
                        assert min(values.values())>0
                        env=numeric_outer(values,cc)
                        assert env['bounded']+t==q
                        assert all(env[a]==env[b] for a,b in OUTER_EQUALITIES if (a,b)!=('bounded','q'))
                        # Exact bridge on these same q,P,C,Z,W; the synthetic
                        # Pell parameters are not claimed to solve the full kernel.
                        A0=10*q+11;J0=t+5
                        mu,kappa=exponent.pell(A0,t);c=exponent.pell(A0,J0)[1]
                        delta,rem=divmod(kappa-t,A0-1);assert rem==0
                        H=A0*A0-1-(A0-P)**2
                        rho,rem=divmod(mu-W-kappa*(A0-P),H);assert rem==0
                        phi=c-kappa;assert min(mu,kappa,delta,rho,phi)>0
                        assert t<q and 0<t<J0<A0-1 and W<q<A0<H
                        env.update(x=x,a=A0-2,A=A0*A0-1,c=c,kappa=kappa,mu=mu,delta=delta,phi=phi,rho=rho)
                        baseline.run_schedule(ADAPTER,env)
                        assert env['raw_bound']==q and env['index_rhs']==kappa and env['pell_gap']==c
                        assert env['mu2']==env['norm_rhs'] and env['exponent_rhs']==mu
                        bad_mu,bad_kappa=exponent.pell(A0,t-1)
                        assert (bad_mu-W-bad_kappa*(A0-P))%H!=0;wrong_inputs+=1
                        # Duplicate either genuine marker at another cell.
                        for marker_state in (0,1):
                            bad=list(cells);bad[1]+=R**marker_state-R**2
                            badC,_,_,_=actual_field(cc,bad,h);badZ=badC-R-W
                            assert badZ>0 and badZ&(cc.MC*J)!=0;mutations+=1
                        # An unoccupied ordinary cell passes the low mask but
                        # must fail occupancy propagation in the field mask.
                        bad=list(cells);bad[1]-=R**2
                        badC,_,_,badF=actual_field(cc,bad,h);badZ=badC-R-W
                        assert badZ>0 and badZ&(cc.MC*J)==0 and badF&(cc.MF*J)!=0
                        mutations+=1
                        if allowed is not None and extra==1:
                            assert any((states[i],states[(i+h)%N],states[(i+h+1)%N]) not in allowed for i in range(N))
                            reverse_rejections+=1
                        max_q_bits=max(max_q_bits,q.bit_length());max_kappa_bits=max(max_kappa_bits,kappa.bit_length())
                        cases+=1
        records.append(dict(name=name,k=3,cell_bits=cc.d,mask_bits=cc.m))
    assert nondivisible_Z>0 and reverse_rejections>0
    # With only End and Start states, two uniqueness insertions cannot cover
    # N>=4 occupied cells. The scalar occupancy clauses reject an empty third.
    cc=compile_rule(2,None)
    assert not unique.previous.scalar_truth(cc,None,((0,1),(0,0),(1,0)))
    return dict(cases=cases,nondivisible_Z_cases=nondivisible_Z,rejected_duplicate_or_empty_mutations=mutations,
                rejected_reversed_transport_cases=reverse_rejections,rejected_wrong_raw_inputs=wrong_inputs,
                max_q_bits=max_q_bits,max_bridge_kappa_bits=max_kappa_bits,examples=records,
                mixed_dummy_bits_at_both_markers=True,k2_no_ordinary_state_obstruction_checked=True,
                full_packed_kernel_tuples_materialized=False,
                scope='Exact common outer/marker/adapter values; moderate independent bridge Pell parameters; full kernel converse is proved symbolically')


def verify():
    return dict(status='PASS_FIXED_RAW_UNIVERSAL84',source=verify_source(),scalar=verify_scalar(),
                composed_interfaces=verify_composed_interfaces(),proof='../1980/FIXED_RAW_UNIVERSAL_84_PROOF.md',
                complete_fixed_index_raw_input_universal_certificate=True,proof_assistant_verified=False,
                scope='Complete positive fixed-index raw-input theorem, with symbolic source and bounded compiler/composition verification')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',result['composed_interfaces']['cases'],'composed interfaces')
