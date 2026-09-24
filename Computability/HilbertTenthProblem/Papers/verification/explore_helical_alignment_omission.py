#!/usr/bin/env python3
"""Complete scoped counter to deleting temporal alignment from the82 source."""
from pathlib import Path
from itertools import product
import json
import sys
import sympy as sp

import explore_fixed_base_exponent_bridge as base
import explore_fixed_raw_universal_84 as compiler
import explore_helical_unary_tableau as tableau
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
NAMES=[name for name in base.NAMES if name!='align']
CONSTANTS=list(base.CONSTANTS)
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANTS+['x']}
SCHEDULE=[row for row in base.SCHEDULE if row[0] not in ('Pm1','alignment')]
EQUALITIES=[pair for pair in base.EQUALITIES if pair!=('alignment','Pm1')]


def source_residuals():
    return [expr for i,expr in enumerate(base.source_residuals()) if i!=2]


def verify_source():
    env=base.fixed_environment(SYM);baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(primitives)==80 and counts=={'+':37,'*':43}
    assert len(NAMES)==len(set(NAMES))==32 and len(sources)==len(EQUALITIES)==20
    assert all(SYM.get('align',sp.Symbol('align')) not in expr.free_symbols for expr in sources)
    return dict(operations=80,multiplications=43,additions_subtractions=37,
                positive_existential_unknown_count=32,equations=20,positive_unknowns=NAMES,
                primitive_instructions=primitives,sources=records,
                deleted_instructions=['Pm1=P-1','alignment=(B-1)*align'],
                deleted_equation='alignment=Pm1',complete_raw_input_universal_certificate=False,
                status='FALSE: temporal alignment cannot be omitted')


def packed_counter(cc,states,nextstates,x,cellshift=0):
    k,m,R,B=cc.k,cc.m,cc.R,cc.B;N=len(states);t=x+2
    assert m>=3*k-3 and N>t>=3 and len(nextstates)==N
    s=2*k-1;aa=m-k+2
    assert k<=aa and aa+k-1<=m+1 and k<=s and s+k-1<=m+1
    genuine=[R**state for state in states];nextgenuine=[R**state for state in nextstates]
    # Shift B^cellshift R^s. Store each independent successor in a high dummy band.
    cells=[genuine[i]+R**aa*nextgenuine[(i+cellshift+1)%N] for i in range(N)]
    ycells=[nextgenuine[i]+R**s*genuine[(i-cellshift)%N] for i in range(N)]
    assert all(0<cell<B-1 for cell in cells+ycells)
    pack=lambda seq:sum(value*B**i for i,value in enumerate(seq))
    C=pack(cells);Y=pack(ycells);RR=pack(cells[-1:]+cells[:-1])
    q=B**N;D=q-1;J=D//(B-1);P=B**cellshift*R**s
    assert 1<P<q and q%P==0 and (P-1)%(B-1)!=0
    assert P*C%D==Y and B*C%D==RR
    W=B**t;Z=C-R-W;u=cc.d*t
    assert states.count(1)==states.count(0)==1 and states[0]==1 and states[t]==0
    assert 0<Z<C<q and Z%2==0 and Z&(cc.MC*J)==0
    F=cc.Ds[0]*C+cc.Ds[1]*RR+cc.Ds[2]*Y
    assert F==pack([cc.Ds[0]*cells[i]+cc.Ds[1]*cells[(i-1)%N]+cc.Ds[2]*ycells[i] for i in range(N)])
    assert 0<F<q-1 and F&(cc.MF*J)==0
    kR=(B*C-RR)//D;kY=(P*C-Y)//D
    zquot=cc.Ds[1]*kR+cc.Ds[2]*kY
    assert kR>0 and kY>0 and zquot>0
    alpha=q-C-u;assert alpha>0 and u<q and 0<W<q
    r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
    assert r%2 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
    values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,F=F,alpha=alpha,zquot=zquot,
                Z=Z,W=W,r=r,x=x)
    env=base.fixed_environment(dict(compiler.constants(cc),cell_bits=cc.d,**values))
    baseline.run_schedule([row for row in base.OUTER if row[0] not in ('Pm1','alignment')],env)
    assert env['bounded']+u==q
    assert all(env[a]==env[b] for a,b in base.previous.OUTER_EQUALITIES
               if (a,b) not in (('alignment','Pm1'),('bounded','q')))
    # Fresh full positive Pell extension and fixed-base bridge follow from
    # these checked range/parity/divisibility hypotheses, without P alignment.
    return dict(raw_x=x,N=N,cellshift=cellshift,cell_bits=cc.d,mask_bits=m,
                P_binary_exponent=P.bit_length()-1,P_aligned=False,
                q_bits=q.bit_length(),r_bits=r.bit_length(),r_population=r.bit_count(),
                required_population=3*cc.d*N,all_outer_coordinates_positive=True,
                exact_outer_equations=True,full_positive_kernel_extension_hypotheses=True,
                full_packed_kernel_tuple_materialized=False)


def verify_counters():
    records=[];statecases=0
    for k in (3,4):
        # This fixed relation has no marked cyclic model: next is always End.
        allowed=frozenset((c,r,0) for c in range(k) for r in range(k))
        cc=compiler.compile_rule(k,allowed)
        assert cc.m>=3*k-3
        for x in range(1,4):
            t=x+2
            for extra in (1,2):
                N=t+extra;states=[1]+[2]*(N-1);states[t]=0
                nextstates=[0]*N
                for cellshift in (0,1):
                    records.append(packed_counter(cc,states,nextstates,x,cellshift));statecases+=N
        # Independently synthesized successor planes can also vary by cell.
        full=compiler.compile_rule(k,None)
        if full.m>=3*k-3:
            states=[1,2,2,0,2];nextstates=[(i+1)%k for i in range(5)]
            records.append(packed_counter(full,states,nextstates,1));statecases+=5
    assert records and all(row['r_population']==row['required_population'] for row in records)
    return dict(cases=len(records),local_state_instances=statecases,records=records,
                exact_false_relation='Allowed triples iff next=End; any genuine cyclic next shift would force every cell End, contradicting Start',
                includes_P_larger_than_B=True)


def verify_tableau_slabs():
    cases=nonhalting=triples=0;records=[]
    for modulus,residue in ((1,0),(2,0),(3,1),(5,2)):
        machine=tableau.unary.residue_machine(modulus,residue)
        S,E=tableau.unary.fixed_markers(machine);pred=tableau.predicate(machine)
        assert S[:6]!=E[:6]
        for x in range(1,5):
            t=x+2;history=tableau.unary.history_for(machine,t,limit=20)
            # Only two transitions are used; acceptance in any last row is absent.
            prefix=history[:3];wmin,hmin=tableau.unary.thresholds(prefix,t)
            for margin in (0,2):
                width=wmin+margin;height=max(4,hmin)
                grid=tableau.strip_array(machine,t,prefix,width,height)
                xS=width-3
                def at(x,y):return grid[y][x%width]
                def window(x,y):return tuple(at(x+dx,y+dy) for dy in (-1,0,1) for dx in (-1,0,1))
                current=[window(xS-i,1) for i in range(width)]
                nxt=[window(xS-i,2) for i in range(width)]
                assert all(pred(block) for block in current+nxt)
                assert current[0]==S and current[t]==E and current.count(S)==current.count(E)==1
                assert all(tableau.unary.blocks.three_valid(current[i],current[(i-1)%width],nxt[i],pred) for i in range(width))
                # For every(center,right), at least one of S,E is forbidden as
                # next because their top two rows differ. This yields >=k^2
                # forbidden clauses for the full alphabet, without enumerating it.
                assert all(not (tableau.unary.blocks.three_valid(c,r,S,pred) and
                                tableau.unary.blocks.three_valid(c,r,E,pred))
                           for c in current+nxt for r in current+nxt)
                halted=history[-1][2]==machine.halt
                nonhalting+=not halted;cases+=1;triples+=width
                records.append(dict(modulus=modulus,residue=residue,raw_x=x,width=width,
                                    machine_halts=halted,valid_initial_next_slab=True,
                                    unique_Start_and_End=True))
    assert nonhalting>0
    return dict(cases=cases,nonhalting_cases=nonhalting,local_triples=triples,records=records,
                full_alphabet_not_enumerated=True,
                full_compiler_population_bound='m>=k^2>=3k-3 since S and E have distinct top two rows')


def verify():
    return dict(status='PASS_HELICAL_ALIGNMENT_OMISSION_COUNTER',source=verify_source(),
                arithmetic_counters=verify_counters(),fixed_tableau_slabs=verify_tableau_slabs(),
                proof='../1980/EXPLORATION_HELICAL_ALIGNMENT_OMISSION.md',
                scope='Deleting the two P-alignment operations admits independent successor planes through dummy-bit wrap; full positive extension proved, not materialized')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['arithmetic_counters']['cases'],'arithmetic cases;',
          result['fixed_tableau_slabs']['nonhalting_cases'],'nonhalting initial slabs')
