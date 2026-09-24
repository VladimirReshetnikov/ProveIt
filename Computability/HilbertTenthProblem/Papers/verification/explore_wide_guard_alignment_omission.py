#!/usr/bin/env python3
"""Wider guards/highest Start do not make the native temporal shift aligned."""
from pathlib import Path
from itertools import product
import json
import sys
import sympy as sp

import explore_fixed_raw_universal_81 as source81
import explore_fixed_raw_universal_84 as native
import explore_helical_unary_tableau as helical

OUT=Path(__file__).with_suffix('.json')
NAMES=[name for name in source81.NAMES if name!='align']
CONSTANTS=list(source81.CONSTANTS)
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANTS+['x']}
SCHEDULE=[row for row in source81.SCHEDULE if row[0] not in ('Pm1','alignment')]
EQUALITIES=[pair for pair in source81.EQUALITIES if pair!=('alignment','Pm1')]


def verify_source():
    env=source81.fixed_environment(SYM)
    source81.bridge.baseline.run_schedule(SCHEDULE,env)
    sources=[expr for i,expr in enumerate(source81.source_residuals()) if i!=2]
    u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(u*u-SYM['y_aux']**2);records=[]
    for i,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if i==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=source81.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==79 and counts=={'+':36,'*':43}
    assert len(NAMES)==len(set(NAMES))==32 and len(sources)==len(EQUALITIES)==20
    return dict(operations=79,multiplications=43,additions_subtractions=36,
                positive_existential_unknown_count=32,equations=20,positive_unknowns=NAMES,
                primitive_instructions=primitives,sources=records,
                status='FALSE: increasing zero guard and relocating Start do not replace P alignment')


def guarded_compile(k,allowed,guard,order):
    old=native.compile_rule(k,allowed)
    clauses=list(old.clauses)
    if order=='reverse':clauses.reverse()
    if order=='rotate':clauses=clauses[2:]+clauses[:2]
    c=tuple(sum(weights[i]*old.A**j for j,(weights,mask) in enumerate(clauses)) for i in range(3*k))
    mu=sum(mask*old.A**j for j,(_,mask) in enumerate(clauses))
    m=mu.bit_count();assert m==old.m and min(c)>0
    target=max((m+2)*sum(c),mu)+2;R=1<<((target-1).bit_length())
    L={'minimum':k+m+1,'wide':max(k+m+1,2*(m+2)),
       'wider':max(k+m+1,2*(m+2))+7}[guard]
    B=R**L;d=B.bit_length()-1;p=k-1
    Ds=tuple(sum(c[site*k+i]*R**(p-i) for i in range(k)) for site in range(3))
    MC=B-1-sum(R**j for j in range(m+2) if j not in (0,p));MF=mu*R**p
    assert 0<MC<=B-2 and 0<MF<=B-2 and MC%2 and MF%2==0
    assert MC.bit_count()+MF.bit_count()==d
    return native.Compiled(k,old.A,tuple(clauses),c,mu,m,old.padding,R,B,d,Ds,MC,MF),L


def arithmetic_case(cc,L,states,nextstates,x,cellshift):
    k,m,R,B=cc.k,cc.m,cc.R,cc.B;N=len(states);p=k-1
    a=m-k+2;s=L-a
    assert m>=3*k-3 and a>=2*k-1 and s>=2*k-1
    assert a+k-1==m+1 and s+2*p<=L-1
    G=[R**state for state in states];H=[R**state for state in nextstates]
    cells=[G[i]+R**a*H[(i+cellshift+1)%N] for i in range(N)]
    ycells=[H[i]+R**s*G[(i-cellshift)%N] for i in range(N)]
    pack=lambda values:sum(value*B**i for i,value in enumerate(values))
    q=B**N;D=q-1;J=D//(B-1);P=B**cellshift*R**s
    C,Y=pack(cells),pack(ycells);RR=pack(cells[-1:]+cells[:-1])
    assert P*C%D==Y and B*C%D==RR and 1<P<q and q%P==0
    assert (P-1)%(B-1)!=0
    CS=R**p;W=B**x;Z=C-CS-W;u=cc.d*x
    assert states.count(p)==states.count(0)==1 and states[0]==p and states[x]==0
    assert 0<Z<C<q and Z%2==0 and Z&(cc.MC*J)==0
    fdigits=[]
    for i in range(N):
        # Whole local field is bounded even when the successor word is not native.
        polynomial=[0]*L
        sitebits=((states[i],a+nextstates[(i+cellshift+1)%N]),
                  (states[(i-1)%N],a+nextstates[(i+cellshift)%N]),
                  (nextstates[i],s+states[(i-cellshift)%N]))
        for site,positions in enumerate(sitebits):
            for bitpos in positions:
                for j in range(k):polynomial[bitpos+p-j]+=cc.c[site*k+j]
        assert sum(polynomial)==2*sum(cc.c)<=R-2
        phi=cc.c[states[i]]+cc.c[k+states[(i-1)%N]]+cc.c[2*k+nextstates[i]]
        assert polynomial[p]==phi and phi&cc.mu==0
        field=sum(value*R**j for j,value in enumerate(polynomial))
        assert 0<field<=B-2 and field&cc.MF==0
        fdigits.append(field)
    F=pack(fdigits)
    assert F==cc.Ds[0]*C+cc.Ds[1]*RR+cc.Ds[2]*Y and 0<F<q-1
    assert F&(cc.MF*J)==0
    kR=(B*C-RR)//D;kY=(P*C-Y)//D;zquot=cc.Ds[1]*kR+cc.Ds[2]*kY
    assert kR>0 and kY>0 and zquot>0
    if cellshift==0:assert kY==H[0]
    alpha=q-C-u;assert alpha>0 and W<q and u<q
    r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
    assert r%2 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
    values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,F=F,alpha=alpha,zquot=zquot,
                Z=Z,W=W,r=r,x=x)
    constants=dict(native.constants(cc),CS=CS,cell_bits=cc.d)
    env=source81.fixed_environment(dict(constants,**values))
    outer=[row for row in source81.OUTER if row[0] not in ('Pm1','alignment')]
    source81.bridge.baseline.run_schedule(outer,env)
    assert env['bounded']+u==q
    assert all(env[left]==env[right] for left,right in source81.bridge.previous.OUTER_EQUALITIES
               if (left,right) not in (('alignment','Pm1'),('bounded','q')))
    native_mask=B-1-sum(R**j for j in range(m+2))
    ytyped=Y&(native_mask*J)==0
    if L>=2*(m+2):assert not ytyped
    return dict(k=k,m=m,L=L,raw_x=x,N=N,cellshift=cellshift,
                C_native=True,Y_native=ytyped,Start_slot=p,End_slot=0,
                dummy_offset=a,shift_inner_digits=s,P_aligned=False,
                cell_bits=cc.d,r_population=r.bit_count(),required_population=3*cc.d*N,
                exact_outer_equalities=True,all_outer_coordinates_positive=True,
                full_positive_kernel_extension_hypotheses=True,
                full_packed_kernel_tuple_materialized=False)


def verify_arithmetic():
    records=[]
    for k in (3,4):
        allowed=frozenset((c,r,0) for c in range(k) for r in range(k))
        for guard,order in product(('minimum','wide','wider'),('original','reverse','rotate')):
            cc,L=guarded_compile(k,allowed,guard,order)
            for x,cellshift in product((1,2),(0,1)):
                N=x+3;states=[k-1]+[1]*(N-1);states[x]=0;nextstates=[0]*N
                record=arithmetic_case(cc,L,states,nextstates,x,cellshift)
                record.update(guard=guard,clause_order=order);records.append(record)
    # A genuinely varying independently synthesized next plane.
    cc,L=guarded_compile(3,None,'wider','reverse')
    record=arithmetic_case(cc,L,[2,0,1,1,1],[0,1,2,0,1],1,0)
    record.update(guard='wider',clause_order='reverse',varying_next_plane=True);records.append(record)
    return dict(cases=len(records),untyped_Y_cases=sum(not row['Y_native'] for row in records),
                records=records,
                false_relation='next is always End; a genuine temporal permutation cannot coexist with Start')


def verify_stay_slabs():
    cases=nonhalting=triples=0;records=[]
    for modulus,residue in ((1,0),(2,0),(3,1),(5,2)):
        machine=source81.residue_machine(modulus,residue)
        S,E=source81.fixed_markers(machine);pred=helical.predicate(machine)
        assert S[:6]!=E[:6]
        for x in range(1,5):
            run=x+1;history=helical.unary.history_for(machine,run,limit=24)
            prefix=history[:3];wmin,hmin=helical.unary.thresholds(prefix,run)
            width=wmin;grid=helical.strip_array(machine,run,prefix,width,max(4,hmin))
            xS=width-4
            def window(x,y):return tuple(grid[y+dy][(x+dx)%width] for dy in (-1,0,1) for dx in (-1,0,1))
            current=[window(xS-i,1) for i in range(width)]
            nxt=[window(xS-i,2) for i in range(width)]
            assert all(pred(block) for block in current+nxt)
            assert current[0]==S and current[x]==E and current.count(S)==current.count(E)==1
            assert all(helical.unary.blocks.three_valid(current[i],current[(i-1)%width],nxt[i],pred) for i in range(width))
            halted=history[-1][2]==machine.halt
            assert halted==((x+2)%modulus==residue)
            nonhalting+=not halted;cases+=1;triples+=width
            records.append(dict(modulus=modulus,residue=residue,raw_x=x,width=width,
                                machine_halts=halted,valid_initial_next_slab=True,
                                unique_Start_and_End=True))
    assert any(row['modulus']==2 and row['residue']==0 and row['raw_x']==1 and not row['machine_halts'] for row in records)
    return dict(cases=cases,nonhalting_cases=nonhalting,local_triples=triples,records=records,
                full_compiler_population_bound='m>=k^2>=3k-3 from distinct top two rows of S and E',
                full_alphabet_not_enumerated=True)


def verify():
    return dict(status='PASS_WIDE_GUARD_ALIGNMENT_OMISSION_COUNTER',source=verify_source(),
                arithmetic=verify_arithmetic(),stay_step_tableau_slabs=verify_stay_slabs(),
                proof='../1980/EXPLORATION_WIDE_GUARD_ALIGNMENT_OMISSION.md',
                scope='All guard widths L>=k+m+1 and all clause orderings within the unchanged one-target-block linear compiler; not arbitrary encodings')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['arithmetic']['cases'],'arithmetic cases;',
          result['arithmetic']['untyped_Y_cases'],'untyped successor cases;',
          result['stay_step_tableau_slabs']['nonhalting_cases'],'nonhalting slabs')
