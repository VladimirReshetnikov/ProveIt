#!/usr/bin/env python3
"""Exact108: fold the two positive counter guards into their packed block."""
from pathlib import Path
import json
import sympy as sp
import explore_shared_pell_index_offset as old

PROGRAM=old.PROGRAM
ZALL=old.ZALL
FIELDS=old.FIELDS  # All twelve conceptual masks remain, including both guards.
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[name for name in old.OUTER_NAMES if name not in ('B0','B1')]
SYM={name:symbol for name,symbol in old.SYM.items() if name not in ('B0','B1')}
SUB={old.SYM['B0']:SYM['A0']+SYM['T'],old.SYM['B1']:SYM['A1']+SYM['T']}


def build():
    previous,pairs,source=old.build()
    powers=[row for row in previous if row[0] in ('q2','q4','q6','D0')]
    removed={'guard0','guard1','raw_packed'}|{row[0] for row in powers}
    removed|={f'pack_product{i}' for i in range(6,11)}
    removed|={f'pack_sum{i}' for i in range(6,10)}
    replacement=[
        ('q_plus_one','+','q',1),
        ('q2_plus_one','+','q2',1),
        ('guard_A1_shift','*','q2','A1'),
        ('guard_A_pair','+','A0','guard_A1_shift'),
        ('guard_A_scaled','*','q_plus_one','guard_A_pair'),
        ('guard_T_scaled','*','q2_plus_one','T'),
        ('guard_block','+','guard_A_scaled','guard_T_scaled'),
        ('guard_rest_shift','*','q4','pack_sum5'),
        ('guard_inside','+','guard_block','guard_rest_shift'),
        ('guard_inside_shift','*','q','guard_inside'),
        ('raw_packed','+','Kp','guard_inside_shift')]
    ops=[]
    for row in previous:
        if row[0]=='pack_product0':ops.extend(powers)
        if row[0]=='pack_product6':ops.extend(replacement)
        if row[0] not in removed:ops.append(row)
    origins=[i for i in range(len(source)) if i not in (5,6)]
    return ops,[pairs[i] for i in origins],[sp.expand(source[i].subs(SUB,simultaneous=True)) for i in origins],origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    histogram=old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==108 and counts=={'+':53,'*':55}
    assert len(source)==len(pairs)==24 and len(OUTER_NAMES+CORE_NAMES)==36
    previous=old.build()[2]
    assert all(sp.expand(previous[i].subs(SUB,simultaneous=True))==0 for i in (5,6))
    q=SYM['q'];u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    raw=sum(old.SYM[name]*q**i for i,name in enumerate(FIELDS)).subs(SUB,simultaneous=True)
    assert sp.expand(env['raw_packed']-raw)==0
    assert sp.expand(env['guard_block']-((SYM['A0']+SYM['T'])+q*SYM['A0']+q*q*(SYM['A1']+SYM['T'])+q**3*SYM['A1']))==0
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        extra=source[origins.index(17)]*(u*u-SYM['y_aux']**2) if origin==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-extra)==0,(i,origin)
        assert sp.expand(polynomial-previous[origin].subs(SUB,simultaneous=True))==0
        records.append(dict(index=i,old_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(extra)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'B0','B1','guard0','guard1'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    return dict(status='PASS',operations=108,primitive_histogram=counts,histogram=histogram,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=36,
                equations=24,primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_unknowns=['B0','B1'],deleted_source_indices=[5,6],
                    retained_conceptual_masks=FIELDS,
                    reconstruction='B0=A0+T, B1=A1+T; both positive before any decoding',
                    identical_packed_integer=True,unchanged_other_sources=23),
                scope='Complete source/primitive checks and exact positive-witness elimination from109; no mask is removed and no digit or carry assumption enters the identity.')


def verify_integer_transport():
    cases=positive=nonpowers=overflows=0
    for q in range(2,22):
        for A0 in (-3,0,1,q-1,q,q+1):
            for A1 in (-2,0,1,q,q+2):
                for T in (-1,0,1,q-1,q+3):
                    B0=A0+T;B1=A1+T
                    G=B0+q*A0+q*q*B1+q**3*A1
                    assert G==(q+1)*(A0+q*q*A1)+(q*q+1)*T
                    fields=[1,B0,A0,B1,A1,2,1,3,1,q+1,2,q+3]
                    rest=sum(fields[i]*q**(i-5) for i in range(5,12))
                    raw=sum(value*q**i for i,value in enumerate(fields))
                    assert raw==1+q*(G+q**4*rest)
                    cases+=1
                    positive+=min(A0,A1,T)>0
                    power=q
                    while power%3==0:power//=3
                    nonpowers+=power!=1
                    overflows+=max(fields)>=q
    return dict(exact_signed_integer_cases=cases,positive_reconstruction_cases=positive,
                non_power_of_three_cases=nonpowers,overflowing_field_cases=overflows,
                scope='Direct polynomial identities, including signed entries and overflowing fields; these are not asserted to solve the controller or Pell equations.')


def fresh_canonical_transport(x):
    # The stronger complete110 numeric checker is rerun, rather than a JSON
    # receipt being accepted as a fresh canonical test. Exact symbolic transport
    # above then proves every retained108 residual and identical kernel data.
    row=old.old.canonical(x)
    assert row['outer_residuals']==17 and row['positive_raw_fields']==12
    return dict(**row,fresh_110_outer_residuals=17,transported_109_outer_residuals=16,
                transported_108_outer_residuals=14,supplied_raw_fields=10,
                reconstructed_positive_guards=2,retained_conceptual_masks=12,
                evidence='Fresh complete110 numerical canonical check, followed by freshly checked exact109 and108 source transport; no large Pell tuple is instantiated.')


def verify():
    return dict(status='PASS_GUARD_BLOCK_PACKING_108',arithmetic=verify_certificate(),
                dependency_source_109=old.verify_certificate()['status'],
                integer_transport=verify_integer_transport(),canonical=[fresh_canonical_transport(1),fresh_canonical_transport(2)],
                proof='../1980/EXPLORATION_GUARD_BLOCK_PACKING.md',
                scope='Complete108-operation universal family by an exact positive-witness bijection with109. The established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['integer_transport']);print(result['canonical'])
