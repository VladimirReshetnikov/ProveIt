#!/usr/bin/env python3
"""Exact109: use the existing doubled Pell index to impose the global offset."""
from pathlib import Path
import json
import sympy as sp
import explore_global_native_offset as old


PROGRAM=old.PROGRAM
ZALL=old.ZALL
FIELDS=old.FIELDS
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[name for name in old.OUTER_NAMES if name!='Jwide']
SYM={name:symbol for name,symbol in old.SYM.items() if name!='Jwide'}


def build():
    prior,pairs,source,origins=old.build();ops=[]
    for row in prior:
        if row[0] in ('packed','twice_Jwide','wide_geometry'):continue
        ops.append(row)
        if row[0]=='D0':
            ops.extend([('twice_raw_packed','+','raw_packed','raw_packed'),
                        ('packed_index_rhs','+','D0','twice_raw_packed')])
    pairs=list(pairs[:-1]);source=list(source[:-1])
    pairs[9]=('tr1','packed_index_rhs')
    raw=sum(SYM[name]*SYM['q']**index for index,name in enumerate(FIELDS))
    source[9]=2*SYM['r']+1-SYM['q']**12-2*raw
    return ops,pairs,source


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM)
    histogram=old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==109 and counts=={'+':54,'*':55}
    assert len(source)==len(pairs)==26 and len(OUTER_NAMES+CORE_NAMES)==38
    prior=old.build()[2]
    assert sp.expand(source[9]-2*prior[9]-prior[-1])==0
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),polynomial) in enumerate(zip(pairs,source)):
        extra=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-extra)==0,i
        if i!=9:assert polynomial==prior[i]
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(polynomial),
                            correction=sp.sstr(extra)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'Jwide','packed','twice_Jwide','wide_geometry'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert env['tr1']==2*SYM['r']+1
    assert any('tr1' in row[2:] for row in ops)
    # The positive integer q is already odd by q=2J+1. Substitution of
    # its unique positive full repunit proves the reverse implication.
    wide=(SYM['q']**12-1)/2
    assert sp.expand(prior[-1].subs(old.SYM['Jwide'],wide))==0
    assert sp.expand(2*prior[9].subs(old.SYM['Jwide'],wide)-source[9])==0
    return dict(status='PASS',operations=109,primitive_histogram=counts,histogram=histogram,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=38,
                equations=26,primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_unknown='Jwide',
                    deleted_registers=['packed','twice_Jwide','wide_geometry'],
                    added_registers=['twice_raw_packed','packed_index_rhs'],
                    reused_register='tr1=2r+1, already required by the Pell index',
                    source_identity='new_pack=2*old_pack+old_wide_geometry',
                    unchanged_retained_sources=25),
                scope='Every new source/primitive comparison and both directions of the exact global-offset substitution are checked symbolically. All fixed numerals retain the stated free-numeral convention.')


def verify_integer_transport():
    cases=positive=nonpowers=rejected=0
    for q in range(3,102,2):
        J=(q-1)//2;L=q**12;wide=(L-1)//2
        assert wide>0 and wide==J*sum(q**i for i in range(12))
        patterns=[[1]*12,[J]*12,[1+(i%2)*(J-1) for i in range(12)],
                  [J+1]+[1]*11,[1]*11+[J+1],[q]*12]
        power=q
        while power%3==0:power//=3
        for fields in patterns:
            raw=sum(value*q**i for i,value in enumerate(fields));r=raw+wide
            beta=L-r
            assert 2*r+1==L+raw+raw
            assert r==sum((J+value)*q**i for i,value in enumerate(fields))
            assert 2*wide+1==L and r-raw-wide==0
            if beta>0:
                assert raw<=wide and fields[-1]<=J
                positive+=1
            else:rejected+=1
            for perturbation in (-2,-1,1,2):
                assert 2*(r+perturbation)+1-L-2*raw==2*perturbation
            cases+=1;nonpowers+=power!=1
    return dict(integer_transport_cases=cases,positive_packed_slack_cases=positive,
                non_power_of_three_cases=nonpowers,nonpositive_slacks_identified=rejected,
                perturbed_indices_rejected=4*cases,
                scope='Exact same-value transport on ordinary odd radices, including nonpowers, field overflows and nonpositive packed slacks. This algebra test does not claim these tuples satisfy the controller or Pell subsystem.')


def inherited_canonical_receipt():
    receipt=json.loads(Path(old.__file__).with_suffix('.json').read_text(encoding='utf-8'))
    assert receipt['status']=='PASS_GLOBAL_NATIVE_OFFSET_110'
    assert receipt['arithmetic']['operations']==110
    assert receipt['arithmetic']['unknown_count']==39 and receipt['arithmetic']['equations']==27
    result=[]
    for row in receipt['canonical']:
        assert row['outer_residuals']==17 and row['positive_raw_fields']==12
        result.append(dict(**row,inherited_110_outer_residuals=17,transported_109_outer_residuals=16,
            evidence='Inherited frozen110 full canonical receipt; unchanged packed, raw and Pell coordinates are not numerically recomputed.',
            exact_transport='Delete only Jwide. The freshly checked identity new_pack=2*old_pack+old_wide makes every new outer residual vanish.'))
    return result


def verify():
    return dict(status='PASS_SHARED_PELL_INDEX_OFFSET_109',arithmetic=verify_certificate(),
                integer_transport=verify_integer_transport(),inherited_110_canonical=inherited_canonical_receipt(),
                proof='../1980/EXPLORATION_SHARED_PELL_INDEX_OFFSET.md',
                scope='Complete109-operation universal family by exact positive-witness elimination from110. Arithmetic and transport checks are fresh; unchanged canonical evidence is explicitly inherited. The established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['integer_transport'])
