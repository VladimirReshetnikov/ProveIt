#!/usr/bin/env python3
"""Exact106: combine the guard and program factorizations, sharing q^2+1."""
from pathlib import Path
import json
import sympy as sp
import explore_guard_block_packing as guard
import explore_factored_raw_program_block as program

old=guard.old
PROGRAM=old.PROGRAM
ZALL=old.ZALL
FIELDS=old.FIELDS
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[name for name in guard.OUTER_NAMES if name not in ('PTC','PTV')]
SYM={name:symbol for name,symbol in guard.SYM.items() if name not in ('PTC','PTV')}
SUB=dict(guard.SUB)
SUB.update(program.test_substitution())


def build():
    prior,pairs,source,origins=guard.build();ops=[]
    deleted={'program_support','program_C_lhs','program_C_rhs','marker_forbidden','program_V_rhs',
             'pack_product0','pack_sum0','pack_product1','pack_sum1','pack_product2','pack_sum2','q2_plus_one'}
    for row in prior:
        if row[0]=='pack_product0':
            ops.extend([
                ('program_qV','*','q','PV'),('program_base','+','PC','program_qV'),
                ('q2_plus_one','+','q2',1),('program_repeated','*','q2_plus_one','program_base'),
                ('q_forbidden','*','q',ZALL),('program_offset_coefficient','-','q_forbidden',PROGRAM['S']),
                ('program_offset_product','*','program_offset_coefficient','H'),
                ('program_offset','+','Jrep','program_offset_product'),
                ('program_offset_shift','*','q2','program_offset'),
                ('pack_sum2','+','program_repeated','program_offset_shift')])
        if row[0] not in deleted:ops.append(row)
    keep=[i for i,origin in enumerate(origins) if origin not in (22,23)]
    return ops,[pairs[i] for i in keep],[sp.expand(source[i].subs(SUB,simultaneous=True)) for i in keep],[origins[i] for i in keep]


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==106 and counts=={'+':51,'*':55}
    assert len(source)==len(pairs)==22 and len(OUTER_NAMES+CORE_NAMES)==34
    prior=old.build()[2]
    for i in (5,6,22,23):assert sp.expand(prior[i].subs(SUB,simultaneous=True))==0
    q=SYM['q'];u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    raw=sum(old.SYM[name]*q**i for i,name in enumerate(FIELDS)).subs(SUB,simultaneous=True)
    assert sp.expand(env['raw_packed']-raw)==0
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2) if origin==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,(i,origin)
        assert sp.expand(polynomial-prior[origin].subs(SUB,simultaneous=True))==0
        records.append(dict(index=i,old_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'B0','B1','PTC','PTV','guard0','guard1'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert sum(row[0]=='q2_plus_one' for row in ops)==1
    assert sum('q2_plus_one' in row[2:] for row in ops)==2
    assert sum(row[0]=='q2' for row in ops)==1
    assert ZALL>3*PROGRAM['S']>0
    return dict(status='PASS',operations=106,primitive_histogram=counts,parameters=['x'],
                positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=34,equations=22,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_unknowns=['B0','B1','PTC','PTV'],
                    deleted_109_source_indices=[5,6,22,23],
                    shared_coefficient='q2_plus_one=q^2+1, one addition with two consumers',
                    retained_conceptual_masks=FIELDS,identical_packed_integer=True),
                scope='Full106 schedule and all22 source comparisons checked directly against109 with all four substitutions. Positivity reconstruction is proved before decoding; no semantic mask is omitted.')


def verify_combined_identity():
    cases=positive=slacks=0
    for q in (3,5,9,15,27,81):
        J=(q-1)//2
        for A0,A1,T in ((1,1,1),(q,2,q+1),(-3,2,-1),(0,0,0)):
            for H in (1,J):
                for S in (1,3):
                    for Zstar in (3*S+1,4*S+5):
                        for C,V in ((1,1),(q+1,J),(-2,3)):
                            tc=C+J-S*H;tv=V+Zstar*H
                            fields=[1,A0+T,A0,A1+T,A1,2,1,1,C,V,tc,tv]
                            block=(1+q*q)*(C+q*V)+q*q*(J+(q*Zstar-S)*H)
                            rest=2+q+q*q+q**3*block
                            G=(q+1)*(A0+q*q*A1)+(q*q+1)*T
                            raw=1+q*(G+q**4*rest)
                            assert raw==sum(value*q**i for i,value in enumerate(fields))
                            if min(A0,A1,T,C,V)>0:
                                low=sum(fields[i]*q**i for i in range(8))
                                Q=V+(Zstar-S)*H
                                assert low>0 and raw-Q*q**11==low+C*q**8+V*q**9+(C+J)*q**10+S*H*(q**11-q**10)>0
                                positive+=1
                                if raw<=(q**12-1)//2:
                                    assert Q<=J and J>S*H and tc>0 and tv>0
                                    slacks+=1
                            cases+=1
    return dict(exact_combined_polynomial_cases=cases,positive_low_block_cases=positive,
                positive_packed_bound_cases=slacks,
                scope='Both factorizations are checked together, including signed/formally negative eliminated fields. These finite algebra cases are not full controller witnesses.')


def inherited_canonical_receipt():
    receipt=json.loads(Path(guard.__file__).with_suffix('.json').read_text(encoding='utf-8'))
    assert receipt['status']=='PASS_GUARD_BLOCK_PACKING_108'
    rows=[]
    for row in receipt['canonical']:
        assert row['transported_108_outer_residuals']==14 and row['retained_conceptual_masks']==12
        rows.append(dict(x=row['x'],serial_blocks=row['serial_blocks'],counter_width=row['counter_width'],
                         packed_bits=row['packed_bits'],valuation=row['valuation'],
                         inherited_guard_108_outer_residuals=14,transported_106_outer_residuals=12,
                         supplied_raw_fields=8,reconstructed_positive_fields=4,retained_conceptual_masks=12,
                         evidence='Inherited freshly rerun standalone guard108 canonical receipt. New full polynomial transport is fresh; unchanged large integers are not recomputed.'))
    return rows


def verify():
    return dict(status='PASS_FACTORED_RAW_BLOCKS_106',arithmetic=verify_certificate(),
                dependencies=dict(guard108=guard.verify_certificate()['status'],program108=program.verify_certificate()['status']),
                combined_identity=verify_combined_identity(),
                program_positive_recovery=program.verify_positive_recovery(),
                inherited_canonical=inherited_canonical_receipt(),
                proof='../1980/EXPLORATION_FACTORED_RAW_BLOCKS.md',
                scope='Complete106 universal family by composition of the exact guard/program positive-witness bijections and one shared addition. Established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['combined_identity'])
