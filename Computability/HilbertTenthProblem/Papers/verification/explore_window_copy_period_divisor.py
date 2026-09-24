#!/usr/bin/env python3
"""Deleting P*v=q from the window-copy80 system admits a full false input.

Actual empty-machine constants are handled by the parametric proof. Numerical
tuples below use explicitly labelled surrogate compiler constants; full Pell
witnesses are not materialized.
"""
from pathlib import Path
import json
import sys
import sympy as sp
import explore_fixed_raw_universal_80 as good

NAMES=[name for name in good.NAMES if name!='v']
CONSTANTS=list(good.CONSTANTS)
SYM={name:good.SYM[name] for name in NAMES+CONSTANTS+['x']}
OUTER=[row for row in good.OUTER if row[0]!='Pv']
CORE=list(good.CORE)
ADAPTER=list(good.ADAPTER)
SCHEDULE=OUTER+CORE+ADAPTER
EQUALITIES=[pair for pair in good.EQUALITIES if pair!=('Pv','q')]


def verify_source():
    env=good.fixed_environment(SYM)
    good.previous.bridge.baseline.run_schedule(SCHEDULE,env)
    original=good.source_residuals()
    indexed=[(ix,s) for ix,s in enumerate(original) if ix!=1]
    U=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=original[14]*(U*U-SYM['y_aux']**2)
    records=[]
    for (old_index,source),(left,right) in zip(indexed,EQUALITIES):
        actual=sp.expand(env[left]-env[right])
        adjust=correction if old_index==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0
        records.append(dict(original_index=old_index,equality=[left,right],
                            source_sign=sign,source=sp.sstr(source),
                            correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=good.previous.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==79 and counts=={'+':37,'*':42}
    assert len(NAMES)==32 and len(EQUALITIES)==len(indexed)==20
    assert len(OUTER)==22 and CORE==good.CORE and ADAPTER==good.ADAPTER
    used=set().union(*(s.free_symbols for _,s in indexed))
    assert used.intersection({good.SYM['v']})==set()
    assert {SYM[name] for name in NAMES}<=used
    return dict(operations=79,multiplications=42,additions_subtractions=37,
                positive_existential_unknown_count=32,positive_unknowns=NAMES,
                equations=20,primitive_instructions=primitives,sources=records,
                deleted_source_index=1,deleted_instruction=list(good.OUTER[2]),
                ledger={'outer':22,'retained_kernel':43,'fixed_base_bridge':14},
                status='REJECTED: complete positive false input proved in note')


def verify_empty_machine():
    old=good.previous.unary.old
    states=('q0','q1','loop','halt')
    alphabet=(0,1,2)
    transitions={(state,symbol):('loop',symbol,0)
                 for state in states for symbol in alphabet}
    transitions['q0',1]=('q1',2,0)
    for symbol in alphabet:
        transitions['halt',symbol]=('halt',symbol,0)
    machine=old.Machine(states,alphabet,'q0','halt',0,transitions)
    reachable={'q0'}
    while True:
        enlarged=reachable|{machine.delta(state,symbol)[0]
                            for state in reachable for symbol in alphabet}
        if enlarged==reachable:break
        reachable=enlarged
    assert machine.halt not in reachable
    Start,End=good.previous.fixed_markers(machine)
    blank=old.tile(0,0,(0,None))
    third=(blank,)*9
    pred=good.previous.helical.predicate(machine)
    assert len({Start,End,third})==3
    assert all(pred(window) for window in (Start,End,third))
    return dict(reachable_states=sorted(reachable),unreachable_halt=machine.halt,
                checked_transition_entries=len(transitions),allowed_distinct_windows=3,
                ordering=['End selector0','Start selector1','blank selector2'],
                actual_full_window_alphabet='Finite effective enumeration, not materialized',
                halting_language='empty for every input')


def verify_parametric_identities():
    B,R,J,K=sp.symbols('B R J K',integer=True)
    q=(B-1)*J+1
    c0=1+R+R**2
    C=B+R+R**2
    F=c0*J
    P=J-K
    identities=[C-(B-1)-c0,(K+P)*C-F-(q-1),C-R-R**2-B]
    assert all(sp.expand(value)==0 for value in identities)
    # The congruence needed for alignment is N == K+1 modulo B-1.
    assert sp.expand((K+B)-(K+1)-(B-1))==0
    return dict(symbolic_identities=4,
                actual_exponent='N=K+B',
                general_exponent_hypotheses=['N>=4','N=K+1 mod(B-1)','J>K+B'],
                supplied_period='P=J-K',transport_quotient=1)


def verify_surrogates():
    records=[];cases=0;min_population=None
    for inner_bits in (1,2,3):
        R=2**inner_bits
        for d in range(3*inner_bits+1,14):
            B=2**d
            # These masks have the same relevant range, parity, population and
            # low-bit properties. They are NOT the actual window-copy compiler.
            MC=B-1-R**2
            MF=R**3
            assert 0<MC<=B-2 and MC%2==1 and 0<MF<=B-2 and MF%2==0
            assert MC.bit_count()+MF.bit_count()==d
            assert R**2&MC==0 and (1+R+R**2)&MF==0
            for DC,DR in ((2,2),(2,4),(4,2),(4,6)):
                K=DC+B*DR
                assert K%2==0 and 0<DC<B and 0<DR<B
                N=DC+DR+1
                q=B**N;J=(q-1)//(B-1)
                assert N>=4 and (N-K-1)%(B-1)==0 and J>K+B
                P=J-K
                align=(P-1)//(B-1)
                c0=1+R+R**2
                C=B+R+R**2;Z=R**2;W=B;F=c0*J
                alpha=q-C-d
                packed=Z+q*F
                mask=(MC+q*MF)*J
                r=(q*q-packed)*(q*q-1)+mask
                values=dict(q=q,P=P,C=C,Jrep=J,align=align,F=F,alpha=alpha,
                            zquot=1,Z=Z,W=W,r=r,x=1)
                constants=dict(B=B,CS=R,DC=DC,DR=DR,MC=MC,MF=MF,cell_bits=d)
                env=good.fixed_environment({**values,**constants})
                good.previous.bridge.baseline.run_schedule(OUTER,env)
                assert env['bounded']+d==q
                for left,right in EQUALITIES[:6]:
                    if left!='raw_bound':assert env[left]==env[right]
                assert min(values.values())>0 and 0<d<q
                assert P>B and P%2==1 and q%P!=0
                assert (B-1)*align==P-1 and W==B**values['x']
                assert 0<Z<C<q and 0<F<q-1 and C<2*B
                assert Z&(MC*J)==0 and F&(MF*J)==0 and packed&mask==0
                assert 0<packed<q*q and 0<mask<q*q-1
                assert q*q<=r<q**4 and r%2==1 and r.bit_count()==3*d*N
                assert r>q and 2**d==W
                # Local occupancy really is malformed: the low cell contains
                # two selector bits. No claim that surrogate masks encode it.
                assert C%B==R+R**2
                cases+=1
                min_population=r.bit_count() if min_population is None else min(min_population,r.bit_count())
                if (inner_bits,d)==(1,4):
                    records.append(dict(R=R,B=B,DC=DC,DR=DR,K=K,N=N,q=q,J=J,P=P,
                                        align=align,C=C,Z=Z,W=W,F=F,alpha=alpha,r=r,
                                        index_population=r.bit_count(),index_parity=r%2))
    return dict(cases=cases,minimum_index_population=min_population,examples=records,
                scope='Surrogate constants only; each retained outer equality and raw exponent checked exactly',
                full_kernel='Fresh positive coordinates established parametrically, not materialized')


def verify():
    return dict(status='PASS_REJECTED_WINDOW_COPY79_PERIOD_DIVISOR',source=verify_source(),
                empty_machine=verify_empty_machine(),parametric=verify_parametric_identities(),
                numerical=verify_surrogates(),proof='../1980/EXPLORATION_WINDOW_COPY_PERIOD_DIVISOR.md',
                conclusion='P*v=q is essential for this deletion; the resulting79 system falsely accepts x=1 for the empty machine',
                review='Author and independent complete proof/source reviews pass; full actual-compiler counterexample proved parametrically')


if __name__=='__main__':
    result=verify()
    output=Path(__file__).with_suffix('.json')
    if sys.argv[1:]==['--write']:
        output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(output.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['numerical']['cases'])
