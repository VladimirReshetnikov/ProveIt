"""Reuse an AND input sum in the checksum: AND63/64 and batches117/119.

The compared parent circuits, complete positive domains and all external
history assumptions are preserved. This is not a universal certificate.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_masked_selection65 as parent

VARIANTS={
    'and63': (False,False,True,63,32,31,22,15,28),
    'and64_prescribed': (False,False,False,64,33,31,22,16,28),
    'general117': (True,False,True,117,55,62,30,23,112),
    'general119_prescribed': (True,False,False,119,57,62,30,24,112),
    'exclusive117': (True,True,True,117,55,62,23,16,112),
    'exclusive119_prescribed': (True,True,False,119,57,62,23,17,112),
}


def source(name):
    batch,exclusive,unbounded,*_=VARIANTS[name]
    old,pairs=(parent.batch_source(exclusive,unbounded) if batch else parent.and_source(unbounded))
    final='q' if unbounded else 'bs_q'
    removed={'input_A','bs_sum01','bs_sum012','bs_Q',final}
    retained=[row for row in old if row[0] not in removed]
    assert len(retained)==len(old)-5
    place=next(i for i,row in enumerate(retained) if row[0]=='F3')+1
    shared=[('input_A','+','F1','F3'), ('shared_sum02','+','F0','F2'),
            ('bs_Q','+','shared_sum02','input_A'), (final,'+','bs_Q',1)]
    new=retained[:place]+shared+retained[place:]
    assert len(new)==len(old)-1
    return new,pairs,old


def domains(name):
    batch,exclusive,unbounded,*_=VARIANTS[name]
    parameters=(parent.BATCH_PARAMETERS if batch else parent.AND_PARAMETERS[1:]
                if unbounded else parent.AND_PARAMETERS)
    auxiliaries=parent.AUX+(['bound_global'] if exclusive else
                          [f'bound{i}' for i in range(8)] if batch else [])
    return parameters,auxiliaries


def audit(name):
    batch,exclusive,unbounded,cost,M,A,witnesses,equations,degree=VARIANTS[name]
    new,pairs,old=source(name)
    parameters,auxiliaries=domains(name)
    assert len(auxiliaries)==witnesses and len(pairs)==equations
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in new)
    assert (len(new),counts['M'],counts['A'])==(cost,M,A)
    symbolic={key:sp.Symbol(key) for key in parameters+auxiliaries}
    oldenv=parent.execute(old,symbolic);newenv=parent.execute(new,symbolic)
    common=oldenv.keys() & newenv.keys()
    assert all(sp.expand(oldenv[key]-newenv[key])==0 for key in common)
    assert all(sp.expand(oldenv[a]-oldenv[b]-newenv[a]+newenv[b])==0 for a,b in pairs)
    assert sp.expand(newenv['bs_Q']-sum(newenv[f'F{i}'] for i in range(4)))==0
    # Against the original selector residuals, including its auxiliary correction.
    raw=dict(symbolic,q=newenv['q'],F3=newenv['F3'])
    expected=parent.native.independent_sources(raw)
    indices=[i for i in range(14) if not(unbounded and i==1)]
    u=symbolic['j']*symbolic['c']-(2*symbolic['r']+1)
    correction=expected[11]*(u*u-symbolic['y_aux']**2)
    for (a,b),index in zip(pairs,indices):
        assert sp.expand(newenv[a]-newenv[b]-expected[index]-(correction if index==12 else 0))==0
    if unbounded:assert sp.expand(expected[1])==0
    rng=random.Random(63117119+cost+equations)
    positive=signed=0
    sos,out=parent.sos_source(new,pairs)
    soscounts=Counter('M' if op=='*' else 'A' for _,op,_,_ in sos)
    assert len(sos)==cost+3*equations-1
    assert soscounts=={'M':M+equations,'A':A+2*equations-1}
    for case in range(512):
        values={key:rng.randrange(1,15) if case<384 else rng.randrange(-8,9)
                for key in parameters+auxiliaries}
        a=parent.execute(old,values);b=parent.execute(sos,values)
        residuals=[a[left]-a[right] for left,right in pairs]
        assert residuals==[b[left]-b[right] for left,right in pairs]
        assert b[out]==sum(value*value for value in residuals)
        if case<384:
            assert b['F3']>=8 and b['bs_Q']>=11
            assert b['q']>=12 if unbounded else b['q']>=16
            positive+=1
        else:signed+=1
    t=sp.Symbol('t')
    weights={key:1+i%4 for i,key in enumerate(parameters+auxiliaries)}
    values={key:sp.Poly(weights[key]*t+i+2,t) for i,key in enumerate(parameters+auxiliaries)}
    env=parent.execute(sos,values);poly=sp.Poly(env[out],t)
    qtop=sp.Poly(env['q'],t).LC()
    top=weights['w']**4*weights['s']**8*weights['k']**4*qtop**12
    assert poly.degree()==degree and poly.LC()==top
    return dict(operations=cost,multiplications=M,additions_subtractions=A,
                parameters=parameters,strictly_positive_auxiliaries=auxiliaries,
                witnesses=witnesses,equations=equations,comparisons=pairs,source=new,
                all_common_registers_symbolically_identical=True,
                complete_comparison_residuals_symbolically_identical=True,
                native_selector_residual_indices=indices,
                arbitrary_assignment_cases=dict(positive=positive,signed=signed),
                sum_of_squares=dict(operations=len(sos),multiplications=soscounts['M'],
                                    additions_subtractions=soscounts['A'],exact_degree=degree,
                                    output=out,weighted_leading_coefficient=str(top)))


def canonical_history_checks():
    """Zero internal digits are allowed; the whole supplied history is positive."""
    rng=random.Random(11711900);records=[]
    slots=(1,1,0,0,3,3,2,2)
    for exclusive in (False,True):
        count=zero_digit_cases=0
        for _ in range(768):
            bits=rng.randrange(4,8) if exclusive else rng.randrange(1,7)
            B=1<<bits;t=rng.randrange(1,9);P=B**t
            margin=B//2 if exclusive else B
            digits=[[rng.randrange(margin) for _ in range(t)] for i in range(4)]
            for row in digits:
                if not any(row):row[0]=1
            if exclusive:
                labels=[rng.randrange(9) for _ in range(t)]
                masks=[[int(label==i+1) for label in labels] for i in range(8)]
            else:masks=[[rng.randrange(2) for _ in range(t)] for i in range(8)]
            H=[parent.packed(row,B) for row in digits]
            S=[parent.packed(row,B) for row in masks]
            Z=[parent.packed([masks[i][j]*digits[slots[i]][j] for j in range(t)],B) for i in range(8)]
            Hb=sum(H[slots[i]]*P**i for i in range(8))
            Mb=(B-1)*sum(S[i]*P**i for i in range(8))
            Zb=sum(Z[i]*P**i for i in range(8))
            assert Hb&Mb==Zb and all(0<h<P for h in H)
            F=parent.truth_fields(P**8,Hb,Mb)
            inputs=dict(P=P,B=B,**{f'history{i}':h for i,h in enumerate(H)},
                        **{f'Shat{i}':s+1 for i,s in enumerate(S)},
                        **{f'Zhat{i}':z+1 for i,z in enumerate(Z)})
            if exclusive:
                assert 2*sum(Z)<P
                inputs['bound_global']=P-sum(Z)-7
                assert inputs['bound_global']>0
            else:inputs.update({f'bound{i}':P-z for i,z in enumerate(Z)})
            inputs.update({key:1 for key in parent.AUX})
            inputs.update({f'F{i}':F[i] for i in range(3)})
            for prescribed in (False,True):
                name=('exclusive' if exclusive else 'general')+('119_prescribed' if prescribed else '117')
                circuit,pairs,_=source(name);env=parent.execute(circuit,inputs)
                assert env['F3']==F[3] and env['q']==16*P**8
                assert all(env[a]==env[b] for a,b in pairs[14 if prescribed else 13:])
            zero_digit_cases+=any(0 in row for row in digits);count+=1
        records.append(dict(exclusive=exclusive,positive_outer_fixtures=count,
                            fixtures_with_zero_internal_history_digits=zero_digit_cases))
    return records


def verify():
    return dict(status='PASS_NATIVE_BINARY_MASKED_SELECTION63',
                variants={name:audit(name) for name in VARIANTS},
                canonical_histories=canonical_history_checks(),
                complete_projection='Unrestricted AND63; prescribed-scale AND64 with its own P power typing.',
                conditional_projection='Selected-source117/119 still require cell geometry, bounded histories '
                                       'and Boolean selector digits. The exclusive variant pays the aggregate '
                                       'output bound; exclusivity and the half-radix margin are sufficient '
                                       'completeness hypotheses, not inferred typing.',
                limitation='No complete universal computation certificate or new arithmetic lower bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
