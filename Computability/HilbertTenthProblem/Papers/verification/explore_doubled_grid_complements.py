#!/usr/bin/env python3
"""Verified101: doubled six-pair grid packing with controller-first recovery."""
from pathlib import Path
import json
import sympy as sp
import explore_interleaved_grid_complements as old

PROGRAM=old.PROGRAM
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=old.OUTER_NAMES
SYM=old.SYM
DOUBLED=['Jrep','H','Tgap','A0','A1','Kp','Km','Z','Dzero','PC','PV']


def build():
    previous,pairs,source,origins=old.build();ops=[]
    for name,op,left,right in previous:
        if name=='twice_raw_packed':continue
        if name in ('q_rhs','paired_scaled'):left='Jrep'
        if name=='input':op,left,right='*',4,'x'
        if name=='packed_index_rhs':right='raw_packed'
        ops.append((name,op,left,right))
    source=list(source)
    source[origins.index(0)]=SYM['q']-SYM['Jrep']-1
    source[origins.index(7)]+=2*SYM['x']
    source[origins.index(8)]+=2*SYM['x']
    raw=sum(f*SYM['q']**i for i,f in enumerate(old.conceptual_fields()))
    source[origins.index(9)]=sp.expand(2*SYM['r']+1-SYM['q']**12-raw)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==101 and counts=={'+':46,'*':55}
    assert len(pairs)==len(source)==23 and len(OUTER_NAMES+CORE_NAMES)==35
    q=SYM['q'];X=SYM['Km']+q*q*(SYM['Dzero']+q*q*(SYM['A0']+q*q*(SYM['A1']+q*q*(SYM['PC']+q*q*SYM['PV']))))
    raw=sum(f*q**i for i,f in enumerate(old.conceptual_fields()))
    geometry=source[origins.index(0)];flags=source[origins.index(3)];zeros=source[origins.index(21)]
    assert sp.expand(env['raw_packed']-raw+geometry*X+flags+q*q*zeros)==0
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),poly,origin) in enumerate(zip(pairs,source,origins)):
        correction=0
        if origin==9:correction=geometry*X+flags+q*q*zeros
        if origin==18:correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2)
        assert sp.expand(env[left]-env[right]-poly-correction)==0,(i,origin)
        records.append(dict(index=i,old_index=origin,equality=[left,right],source=sp.sstr(poly),correction=sp.sstr(correction)))
    sub={SYM[n]:SYM[n]/2 for n in DOUBLED}
    sub[SYM['alphaI']]=SYM['alphaI']+2*SYM['x']
    prior=old.build()[2];factors=[]
    for i,origin in enumerate(origins):
        transformed=prior[i].subs(sub,simultaneous=True)
        choices=[f for f in (1,2) if sp.expand(source[i]-f*transformed)==0]
        assert len(choices)==1,(i,origin)
        factors.append(dict(index=i,old_index=origin,factor=choices[0]))
    assert PROGRAM['K']>=3 and PROGRAM['g']>0
    assert old.ZON>PROGRAM['g']*(PROGRAM['I']+1)
    # The terminal nozero annotation is a graph property, not a counter fact.
    incoming=[a for a,b in PROGRAM['edges'] if b==0]
    assert incoming and all(PROGRAM['zeros'][a]==0 for a in incoming)
    return dict(status='PASS',operations=101,primitive_histogram=counts,unknown_count=35,
                positive_unknowns=OUTER_NAMES+CORE_NAMES,equations=23,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                inverse_source_factors=factors,doubled_coordinates=DOUBLED,
                terminal_predecessors=incoming,
                scope='Exact101 schedule and all23 source comparisons, including acyclic source corrections and divided-coordinate transport. Evenness and semantic terminal-label recovery are separate general proof obligations.')


def words(m):
    out=[0];power=1
    for _ in range(m):out += [v+power for v in out];power*=3
    return out


def doubled_word(n):
    if n<0 or n%2:return False
    while n:
        n,digit=divmod(n,3)
        if digit not in (0,2):return False
    return True


def verify_carry_lemmas():
    residue_cases=state_pairs=junk_pairs=guard_pairs=negative_guards=geometry=aligned=terminal=0
    for m in range(1,9):
        R=3**m
        for e in range(1,49):
            if 2*(3**e-1)%(R-1)==0:
                assert e%m==0;aligned+=1
            geometry+=1
        for c in words(m):
            for a in range(1,m+1):
                modulus=3**a;residue=(2*c+1)%modulus
                assert residue==0 or residue%2==1
                residue_cases+=1
    for q in (9,27,81,243):
        for SH in (2,6):
            for C in range(1,q):
                tc=SH-C;carry,low=divmod(tc,q);high=C+carry
                assert carry in (-1,0) and 0<=high<q
                if doubled_word(low) and doubled_word(high):
                    if tc<0:assert C%2==1 and doubled_word(C-1)
                    else:assert C%2==0
                    state_pairs+=1
        for zH in (2,6):
            for V in range(1,q+1):
                tv=zH-V;carry,low=divmod(tv,q);high=V+carry
                assert carry in (-1,0) and 0<=high<=q
                if doubled_word(low) and doubled_word(high):
                    if tv<0:assert V%2==1
                    else:assert V%2==0 and V<q
                    junk_pairs+=1
        for t in range(2,max(3,q//3),2):
            for A in range(1,max(2,q//3)):
                E=t-A;carry,low=divmod(E,q);high=A+carry
                assert carry in (-1,0) and 0<=high<q
                if doubled_word(low) and doubled_word(high):
                    if E<0:negative_guards+=1;assert A%2==1
                    else:assert A%2==0
                    guard_pairs+=1
        # A real endpoint alias requires the route-parity argument.
        assert doubled_word(2) and doubled_word(q-1)
        assert (2-q)%q==2 and q+(2-q)//q==q-1
    for R in (27,81,243,729):
        W=R**3
        for u in range(3,16):
            q=R**u;H=2*(q-1)//(R-1)
            assert W*H*R<3*q*(W-1)
            assert (R-3)*q>9*q
            for top in (2,4,6):
                D=top*(q//R);six_t=(R-3)*D
                assert six_t*(W-1)>6*W*H
                terminal+=1
    return dict(odd_successor_residue_cases=residue_cases,
                accepted_state_pair_windows=state_pairs,accepted_junk_pair_windows=junk_pairs,
                accepted_guard_windows=guard_pairs,negative_guard_aliases=negative_guards,
                power_geometry_cases=geometry,aligned_geometry_cases=aligned,
                terminal_gap_bound_cases=terminal,
                isolated_aliases=dict(state=dict(q=27,SH=2,C=3,chunks=[26,2]),
                                      junk=dict(q=27,zH=2,V=27,chunks=[2,26]),
                                      guard=dict(q=27,t=2,A=3,chunks=[26,2])),
                scope='Nonvacuous borrow cases show why controller recovery and the structural terminal label are required. Exact residue, no-outgoing-carry, exponent geometry and terminal bounds corroborate the general proof.')


def verify_terminal_compiler_contract():
    import explore_three_raw_counter_compiler as compiler
    from explore_cyclic_entry_serial_composition import cyclic_graph
    cases=[]
    for register in range(3):
        cases.extend([(('inc',register,'accept'),'inc'),
                      (('dec',register,'accept','accept'),'zero'),
                      (('dec',register,'accept','accept'),'nonzero')])
    cases.append((('jump','accept'),'jump'))
    for instruction,branch in cases:
        phases=compiler.physical_phases(instruction,branch)
        assert len(phases)==2 and phases[1][1]==(0,0,0)
    machine=compiler.sample_machine()
    graph=compiler.serial_graph(machine['code'],machine['start'])
    cyclic=cyclic_graph(graph)
    for sequence in graph['macros'].values():
        assert len(sequence)==6
        assert all(graph['nodes'][node][2]==0 for node in sequence[3:])
    predecessors=cyclic['accept_predecessors']
    assert predecessors and all(cyclic['nodes'][node][2]==0 for node in predecessors)
    assert all(graph['nodes'][node][2]==0 for node in graph['prefix'][3:])
    return dict(instruction_branch_cases=len(cases),compiled_logical_locations=len(machine['code']),
                complete_physical_macros=len(graph['macros']),
                original_serial_nodes=len(graph['nodes']),cyclic_serial_nodes=len(cyclic['nodes']),
                accepting_predecessors=len(predecessors),
                accepting_predecessor_labels=[list(cyclic['nodes'][node]) for node in sorted(predecessors)],
                scope='Calls the actual instruction, serial-graph and cyclic-quotient implementations. Checks terminal labels structurally, without running a Turing-machine trace or assuming counter validity.')


def canonical(x):
    c=PROGRAM;m=max(c['B'],old.EXTRA_EXPONENT+old.ELL);m+=(-m)%old.ELL;R=3**m
    while (R-1)//(old.B0-1)<=old.ZON or R<=4*x:m+=old.ELL;R*=old.B0
    zgrid=(R-1)//(old.B0-1)-old.ZON
    path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;W=R**3;q=R**blocks;j=(q-1)//2;h=(q-1)//(R-1)
    values=[2*x,0,0];a0=a1=kp=km=z0=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        aa,bb=old.ALIGNED.single.split_ternary(n,b);weight=R**b
        a0+=aa*weight;a1+=bb*weight
        if c['signs'][state]>0:kp+=weight
        else:km+=weight
        z0+=c['zeros'][state]*weight;values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and c['zeros'][path[-2]]==0
    d=h-z0;t=((R-3)//6)*d
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*kp-c['hz']*d
    original=[kp,km,z0,d,t-a0,a0,t-a1,a1,c['S']*h-C,C,zgrid*h-V,V]
    fields=[2*f for f in original];raw=sum(f*q**i for i,f in enumerate(fields));L=q**12
    r=(L+raw-1)//2
    vals=dict(x=x,q=q,Jrep=2*j,W=W,H=2*h,v=q//W,R=R,Tgap=2*t,A0=2*a0,A1=2*a1,
              Kp=2*kp,Km=2*km,Z=2*z0,Dzero=2*d,alphaI=R-4*x,PC=2*C,PV=2*V,
              zgrid=zgrid,r=r,beta=L-r)
    assert min(vals.values())>0 and min(fields)>=0
    assert all(f%2==0 and old.old.boolean(f//2,m*blocks) for f in fields)
    assert 2*t>2*(a0+a1) and 2*d>=2*q//R
    assert r==sum(f*q**i for i,f in enumerate(original))+(L-1)//2
    assert old.old.native(r,12*m*blocks) and r%3==2 and r%2==0 and r<L<r*r
    _,_,source,origins=build();sub={SYM[k]:v for k,v in vals.items()}
    outer=[i for i,o in enumerate(origins) if o<10 or o>=20]
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in outer)
    valuation=old.old.central_valuation(r);assert valuation==12*m*blocks
    return dict(x=x,counter_width=m,serial_blocks=blocks,outer_residuals=len(outer),
                doubled_conceptual_fields=12,all_doubled_coordinates_even=True,
                terminal_nozero_label=True,strict_guard_complements=True,
                packed_index_unchanged_from_102_at_same_width=True,
                packed_bits=r.bit_length(),valuation=valuation,
                scope='Fresh complete doubled outer tuple, all12 masks, positive slacks and exact valuation. General positive converse supplies enormous Pell auxiliaries without materializing them.')


def verify():
    return dict(status='PASS_DOUBLED_GRID_COMPLEMENTS_101',arithmetic=verify_certificate(),
                carry_lemmas=verify_carry_lemmas(),terminal_compiler=verify_terminal_compiler_contract(),
                canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_DOUBLED_GRID_COMPLEMENTS.md',
                scope='Complete101 construction with author and three independent full proof/source reviews and fresh verification passing, including the focused generic terminal-compiler check. The established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['primitive_histogram'])
    print(result['carry_lemmas']);print(result['canonical'])
