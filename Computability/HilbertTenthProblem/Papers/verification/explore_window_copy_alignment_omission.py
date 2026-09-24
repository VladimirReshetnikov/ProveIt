#!/usr/bin/env python3
"""False78 obtained by deleting both P-alignment operations from copy80."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import sys
import sympy as sp

import explore_fixed_raw_universal_80 as previous
import explore_fixed_raw_scale_q2 as scale

OUT=Path(__file__).with_suffix('.json')
ROOT=Path(__file__).resolve().parents[2]
NAMES=[n for n in previous.NAMES if n!='align']
SCHEDULE=[row for row in previous.SCHEDULE if row[0] not in ('Pm1','alignment')]
OUTER=SCHEDULE[:21]
EQUALITIES=[pair for pair in previous.EQUALITIES if pair!=('alignment','Pm1')]


def verify_source():
    sources=[s for i,s in enumerate(previous.source_residuals()) if i!=2]
    env=previous.fixed_environment(previous.SYM)
    previous.previous.bridge.baseline.run_schedule(SCHEDULE,env)
    z=previous.SYM;U=z['j']*z['c']-(2*z['r']+1)
    correction=sources[13]*(U*U-z['y_aux']**2)
    records=[]
    for i,((lhs,rhs),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[lhs]-env[rhs]);adjust=correction if i==14 else 0
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,i
        records.append(dict(index=i,equality=[lhs,rhs],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=previous.previous.bridge.verify_primitives(SCHEDULE,env)
    assert counts=={'*':42,'+':36} and len(primitives)==78
    assert len(NAMES)==32 and len(EQUALITIES)==len(sources)==20
    assert len(OUTER)==21 and Counter(row[1] for row in OUTER)['*']==10
    assert all(z['align'] not in s.free_symbols for s in sources)
    assert ('Pv','q') in EQUALITIES and any(row[0]=='n2' for row in SCHEDULE)
    return dict(operations=78,multiplications=42,additions_subtractions=36,
                positive_unknown_count=32,positive_unknowns=NAMES,equations=20,
                deleted_instructions=[r for r in previous.SCHEDULE if r[0] in ('Pm1','alignment')],
                primitive_instructions=primitives,sources=records,
                ledger={'outer':21,'retained_kernel':43,'raw_input_bridge':14},
                retained_period_divisor=True,retained_kernel_scale='q^3')


def initial_slab(x,left=2,right=2):
    old=previous.previous
    machine=scale.empty_machine();pred=old.helical.predicate(machine)
    V,H=old.tile(1,0),old.tile(0,1)
    phases=['L']*left+['I']*(x+1)+['Q']+['R']*right
    center=[V]+[old.tile(0,0,old.unary.phase_payload(p,machine),p) for p in phases]
    N=len(center);blank=(machine.blank,None)
    above=[V]+[H]*(N-1)
    below=[V]
    for col in range(1,N):
        l,r=center[(col-1)%N],center[(col+1)%N]
        payload=old.unary.old.next_payload(blank if l[0] else l[2],center[col][2],
                                          blank if r[0] else r[2],machine)
        assert payload is not None
        below.append(old.tile(0,0,payload))
    slab=[above,center,below];start=left+x+1
    window=lambda col:tuple(slab[t][(col+dx)%N] for t in range(3) for dx in (-1,0,1))
    word=[window((start-i)%N) for i in range(N)]
    S,E=old.fixed_markers(machine)
    assert all(pred(w) for w in word)
    assert word[0]==S and word[x]==E and word.count(S)==word.count(E)==1
    assert all(old.unary.blocks.horizontal(word[i],word[(i-1)%N]) for i in range(N))
    assert all(machine.delta(q,a)[0]!='H' for q in ('q0','q1') for a in machine.alphabet)
    return machine,word,slab


def compile_slab(word):
    # A finite subalphabet of actual allowed windows; the proof treats the full alphabet.
    old=previous.previous
    machine=scale.empty_machine();S,E=old.fixed_markers(machine)
    windows=[E,S]+list(dict.fromkeys(w for w in word if w not in (E,S)))
    tiles=list(dict.fromkeys(tile for window in windows for tile in window))
    coded=[tuple(tiles.index(tile) for tile in w) for w in windows]
    cc=previous.compile_windows(coded,len(tiles))
    return cc,[windows.index(w) for w in word],tiles


def verify_cases():
    records=[];count=vertical_checks=horizontal_checks=unary_checks=0
    for x,left,right in ((1,2,2),(2,3,2),(3,2,3)):
        machine,word,slab=initial_slab(x,left,right)
        cc,states,tiles=compile_slab(word)
        B,R,N=cc.B,cc.R,len(word)
        radix_bits=R.bit_length()-1
        coefficient=lambda value,degree:(value>>(radix_bits*degree))&(R-1)
        P=R**(3*cc.a)
        assert 1<P<B and (P-1)%(B-1)!=0
        assert max(cc.positions)+3*cc.a<cc.H
        for fill in (0,1):
            rows=[cc.bits(s,fill) for s in states]
            cells=[cc.cell(row) for row in rows]
            pack=lambda digits:sum(value*B**i for i,value in enumerate(digits))
            C=pack(cells);Rword=pack([cells[(i-1)%N] for i in range(N)])
            q=B**N;J=(q-1)//(B-1);W=B**x;Z=C-R-W;u=cc.d*x
            Fdigits=[]
            for i,cell in enumerate(cells):
                field=(cc.DC+P)*cell+cc.DR*cells[(i-1)%N]
                assert 0<field<=B-2 and field&cc.MF==0
                bits=dict(zip(cc.positions,rows[i]))
                for rr in range(2):
                    for col in range(3):
                        for symbol in range(cc.a):
                            e=cc.payload[rr,col,symbol]
                            assert coefficient(field,e)==2*bits[cc.payload[rr+1,col,symbol]]
                            vertical_checks+=1
                for rr in range(3):
                    for col in range(2):
                        for symbol in range(cc.a):
                            e=cc.H+cc.payload[rr,col,symbol]
                            assert coefficient(field,e) in (0,2)
                            horizontal_checks+=1
                expected=sum(coefficient*bits[e] for e,coefficient in cc.coeff.items())
                assert coefficient(field,cc.T)==expected
                unary_checks+=1
                Fdigits.append(field)
            F=pack(Fdigits)
            assert F==(cc.DC+P)*C+cc.DR*Rword
            assert 0<P*C<q and q%P==0
            kR,rem=divmod(B*C-Rword,q-1);assert rem==0 and kR>=1
            zquot=cc.DR*kR
            assert Z&(cc.MC*J)==F&(cc.MF*J)==0
            assert 0<Z<C<q and Z%2==0 and 0<F<q-1
            assert C>J and C<=(B-2)*J and J>=W>u
            r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
            assert r%2==1 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
            values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,F=F,alpha=q-C-u,
                        zquot=zquot,Z=Z,r=r,W=W,x=x)
            assert min(values.values())>0
            env=previous.fixed_environment({**cc.constants(),**values})
            previous.previous.bridge.baseline.run_schedule(OUTER,env)
            for i,(lhs,rhs) in enumerate(EQUALITIES[:6]):
                if i==2:assert env['bounded']+u==q
                else:assert env[lhs]==env[rhs],(lhs,rhs)
            assert env['Pv']==q and env['n2']==q**3
            count+=1
            if fill==0:
                records.append(dict(x=x,left=left,right=right,N=N,slab=slab,
                                    finite_allowed_window_alphabet=len(cc.windows),tile_alphabet=tiles,
                                    state_word=states,cell_bits=cc.d,inner_bits=R.bit_length()-1,
                                    P_bits=P.bit_length()-1,q_bits=cc.d*N,index_bits=r.bit_length(),
                                    exact_valuation=r.bit_count(),scale_exponent=3*cc.d*N,
                                    index_sha256=hashlib.sha256(r.to_bytes((r.bit_length()+7)//8,'big')).hexdigest()))
    return dict(positive_outer_cases=count,vertical_double_copy_checks=vertical_checks,
                horizontal_overlap_checks=horizontal_checks,center_clause_checks=unary_checks,
                examples=records,source_period_divisor_retained=True,
                arithmetic_cases_use_actual_allowed_window_subalphabets=True,
                full_machine_alphabet_handled_by_general_proof=True,
                all_dummy_zero_and_one_tested=True)


def verify():
    paths=['Papers/1980/FIXED_RAW_UNIVERSAL_80_PROOF.md',
           'Papers/verification/explore_fixed_raw_universal_80.py',
           'Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md',
           'Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md',
           'Papers/1980/EXPLORATION_FIXED_RAW_SCALE_Q2.md']
    return dict(status='PASS_REJECTED_WINDOW_COPY_ALIGNMENT_OMISSION78',
                source=verify_source(),counterexamples=verify_cases(),
                dependency_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                proof='../1980/EXPLORATION_WINDOW_COPY_ALIGNMENT_OMISSION.md',
                complete_positive_false_input_proved=True,
                full_machine_alphabet_materialized=False,full_packed_Pell_tuple_materialized=False,
                smaller_universal_certificate=False,proof_assistant_verified=False)


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          result['counterexamples']['positive_outer_cases'],'full positive outer tuples')
