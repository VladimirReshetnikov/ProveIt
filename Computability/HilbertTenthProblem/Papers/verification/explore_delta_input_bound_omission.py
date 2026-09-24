#!/usr/bin/env python3
"""Rejected76: dropping dx from the77 raw bound admits a false odd input.

The full-source witness map is symbolic. Numerical bridge examples are not
asserted to materialize the actual enormous compiler/kernel witnesses.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp
import explore_fixed_raw_universal_77 as previous

original81=previous.previous.previous.previous
bridge=original81.bridge
NAMES=list(previous.NAMES)
CONSTANTS=list(previous.CONSTANTS)
SYM=previous.SYM
OUTER=list(previous.OUTER)
CORE=list(previous.CORE)
ADAPTER=[row for row in previous.ADAPTER if row[0]!='raw_bound']
SCHEDULE=OUTER+CORE+ADAPTER
EQUALITIES=[('bounded','q') if pair==('raw_bound','q') else pair for pair in previous.EQUALITIES]


def source_residuals():
    result=previous.source_residuals()
    result[2]=sp.expand(result[2].subs(SYM['x'],0))
    return result


def verify_source():
    env=previous.previous.previous.fixed_environment(SYM)
    bridge.baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();U=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(U*U-SYM['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[left,right],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==76 and counts=={'+':34,'*':42}
    assert len(OUTER)==20 and len(CORE)==43 and len(ADAPTER)==13
    assert len(NAMES)==32 and len(sources)==len(EQUALITIES)==20
    assert CORE==previous.CORE and OUTER==previous.OUTER
    assert {ix for ix,(old,new) in enumerate(zip(previous.source_residuals(),sources)) if sp.expand(old-new)!=0}=={2}
    assert {ix for ix,source in enumerate(sources) if SYM['x'] in source.free_symbols}=={16}
    assert {SYM[name] for name in NAMES}<=set().union(*(source.free_symbols for source in sources))
    return dict(operations=76,multiplications=42,additions_subtractions=34,
                positive_existential_unknown_count=32,positive_unknowns=NAMES,equations=20,
                primitive_instructions=primitives,sources=records,changed_source_index=2,
                raw_input_source_indices=[16],ledger={'outer':20,'kernel':43,'adapter':13},
                deleted_instruction=['raw_bound','+','bounded','scaled_t'])


def verify_full_witness_map():
    a=SYM['a'];D=a*a+4*a+3;d=SYM['cell_bits']
    substitutions={SYM['x']:2+D,SYM['delta']:SYM['delta']-d,SYM['alpha']:SYM['alpha']+2*d}
    for old,new in zip(previous.source_residuals(),source_residuals()):
        transformed=sp.expand(new.subs(substitutions,simultaneous=True))
        assert sp.expand(transformed-old.subs(SYM['x'],2))==0
    return dict(exact_complete_residual_maps=20,accepted_seed_input=2,
                false_input='2+Delta',new_delta='delta-cell_bits',
                new_alpha='alpha+2*cell_bits=q-C',
                unchanged='Every other existential coordinate and every fixed compiler numeral',
                positivity_scope='All changed coordinates proved positive in the note')


def verify_delta_lower_bound():
    cases=steps=0
    for A in range(2,51):
        D=A*A-1
        last_delta=0
        for n in range(1,62,2):
            chi,psi=previous.pell(A,n)
            delta,rem=divmod(psi-n,D);assert rem==0
            assert delta>=2*(n-1)
            if n>1:
                middle_chi,_=previous.pell(A,n-1)
                increment,rem=divmod(2*(middle_chi-1),D);assert rem==0
                assert delta-last_delta==increment and increment>=4
                steps+=1
            last_delta=delta;cases+=1
    return dict(exact_odd_index_cases=cases,exact_growth_steps=steps,
                proven_lower_bound='delta_n >= 2*(n-1) for odd n>=1')


def verify_numeric_maps():
    records=[]
    for b,L in ((1,4),(3,2),(3,4),(5,2),(5,4),(7,2)):
        d=b*L;u=2*d+b;W=2**u
        a=2**(u+3);A=a+2;D=A*A-1;J0=u+2
        mu,kappa=previous.pell(A,u);_,c=previous.pell(A,J0)
        delta,rem=divmod(kappa-u,D);assert rem==0
        rho,rem=divmod(mu-a*kappa-W,4*a+3);assert rem==0
        phi=c-kappa
        B=2**d;q=B**3;C=1+W
        alpha_old=q-C-2*d
        alpha_new=alpha_old+2*d
        false_x=2+D;false_delta=delta-d;false_u=d*false_x+b
        assert min(kappa,mu,delta,rho,phi,alpha_old,alpha_new,false_delta)>0
        assert delta>=2*(u-1)>=4*d>d
        assert false_x%2==1 and D%2==1 and a%2==0
        assert kappa==false_u+false_delta*D
        assert mu*mu==1+D*kappa*kappa and c==kappa+phi
        assert mu==W+a*kappa+rho*(4*a+3)
        assert C+alpha_new==q and W==(2**b)*B**2
        assert false_u%2==1 and d*false_x>q
        records.append(dict(b=b,L=L,d=d,original_index=u,new_input_bits=false_x.bit_length(),
                            new_input_parity=false_x%2,delta_lower_bound=2*(u-1),
                            delta_bits=delta.bit_length(),positive_changed_coordinates=True))
    return dict(examples=records,count=len(records),
                scope='Positive bridge and bound-map examples; C and main Pell parameters are illustrative, not asserted to be full compiled/kernel tuples')


def verify_even_machine():
    machine=original81.residue_machine(2,0)
    assert machine.delta('q0',1)==('prep',2,0)
    assert machine.delta('prep',2)==('s0',2,-1)
    for j in (0,1):
        assert machine.delta('s'+str(j),1)==('s'+str((j+1)%2),1,-1)
        assert machine.delta('s'+str(j),0)==('H' if (j+1)%2==0 else 'loop',0,0)
    assert all(machine.delta('loop',s)==('loop',s,0) for s in machine.alphabet)
    accepted=rejected=0
    for x in range(1,33):
        history=original81.unary.history_for(machine,x+1,limit=2*x+20)
        end=history[-1][2]
        assert end==('H' if x%2==0 else 'loop')
        accepted+=int(x%2==0);rejected+=int(x%2==1)
    return dict(raw_inputs_checked=32,halting_even_inputs=accepted,
                proved_looping_odd_inputs=rejected,seed_input=2,
                machine_language='Positive even integers; scanning invariant proves the unbounded assertion',
                full_compiler='The effective77 compiler for this fixed machine is used analytically, not materialized')


def verify():
    root=Path(__file__).resolve().parents[2]
    dependencies=['Papers/1980/FIXED_RAW_UNIVERSAL_77_PROOF.md',
                  'Papers/verification/explore_fixed_raw_universal_77.py',
                  'Papers/verification/explore_fixed_raw_universal_77.json']
    return dict(status='PASS_REJECTED_DELTA_RAW_BOUND76',source=verify_source(),
                full_source_witness_map=verify_full_witness_map(),
                delta_growth=verify_delta_lower_bound(),numerical=verify_numeric_maps(),
                even_machine=verify_even_machine(),
                dependency_hash_normalization='CRLF normalized to LF before SHA256',
                dependency_sha256={name:hashlib.sha256((root/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for name in dependencies},
                proof='../1980/EXPLORATION_DELTA_INPUT_BOUND_OMISSION.md',
                conclusion='The weakened76 source has a full strictly positive false odd input for a fixed even-input machine',
                review='Author and independent complete proof/source reviews pass; full false input is proved, enormous witnesses are not numerically materialized')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['delta_growth']);print(result['even_machine'])
