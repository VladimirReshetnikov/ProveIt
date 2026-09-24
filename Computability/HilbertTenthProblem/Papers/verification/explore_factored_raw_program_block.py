#!/usr/bin/env python3
"""Exact108: factor the four program fields and recover both test words."""
from pathlib import Path
import json
import sympy as sp
import explore_shared_pell_index_offset as old


PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[name for name in old.OUTER_NAMES if name not in ('PTC','PTV')]
SYM={name:symbol for name,symbol in old.SYM.items() if name not in ('PTC','PTV')}
LOW_FIELDS=old.FIELDS[:8]


def test_substitution():
    return {old.SYM['PTC']:SYM['PC']+SYM['Jrep']-PROGRAM['S']*SYM['H'],
            old.SYM['PTV']:SYM['PV']+ZALL*SYM['H']}


def build():
    prior,pairs,source=old.build();ops=[]
    deleted={'program_support','program_C_lhs','program_C_rhs','marker_forbidden','program_V_rhs',
             'pack_product0','pack_sum0','pack_product1','pack_sum1','pack_product2','pack_sum2','q2'}
    for row in prior:
        if row[0]=='pack_product0':
            ops.extend([('q2','*','q','q'),
                ('program_qV','*','q','PV'),('program_base','+','PC','program_qV'),
                ('q2_plus_one','+','q2',1),('program_repeated','*','q2_plus_one','program_base'),
                ('q_forbidden','*','q',ZALL),('program_offset_coefficient','-','q_forbidden',PROGRAM['S']),
                ('program_offset_product','*','program_offset_coefficient','H'),
                ('program_offset','+','Jrep','program_offset_product'),
                ('program_offset_shift','*','q2','program_offset'),
                ('pack_sum2','+','program_repeated','program_offset_shift')])
        if row[0] not in deleted:ops.append(row)
    newpairs=[];newsource=[];origins=[];sub=test_substitution()
    for index,(pair,p) in enumerate(zip(pairs,source)):
        if index in (22,23):continue
        newpairs.append(pair);newsource.append(sp.expand(p.subs(sub,simultaneous=True)));origins.append(index)
    return ops,newpairs,newsource,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==108 and counts=={'+':53,'*':55}
    assert len(source)==len(pairs)==24 and len(OUTER_NAMES+CORE_NAMES)==36
    prior=old.build()[2];q=SYM['q'];records=[]
    assert sp.expand(source[9]-prior[9]+2*q**10*prior[22]-2*q**11*prior[23])==0
    sub=test_substitution()
    assert sp.expand(prior[22].subs(sub,simultaneous=True))==0
    assert sp.expand(prior[23].subs(sub,simultaneous=True))==0
    u=2*SYM['r']+1+SYM['j']*SYM['c']
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,i
        if origin!=9:assert polynomial==prior[origin]
        records.append(dict(index=i,old_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    C,V,J,H=SYM['PC'],SYM['PV'],SYM['Jrep'],SYM['H']
    block=C+q*V+q*q*(C+J-PROGRAM['S']*H)+q**3*(V+ZALL*H)
    assert sp.expand(env['pack_sum2']-block)==0
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used
    assert not used&{'PTC','PTV','program_support','program_C_lhs','program_C_rhs','marker_forbidden','program_V_rhs'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert ZALL>3*PROGRAM['S']>0
    return dict(status='PASS',operations=108,primitive_histogram=counts,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=36,
                equations=24,primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_unknowns=['PTC','PTV'],deleted_source_indices=[22,23],
                    new_program_block='(1+q²)(C+qV)+q²[J+(q*Zstar-S)H]',
                    old_program_and_definitions_operations=11,new_program_operations=10,
                    reused_power='q2 is moved before packing; its multiplication remains counted once',
                    packing_identity='new_pack=old_pack-2q^10*old_support+2q^11*old_testV'),
                scope='All108 primitive instructions,24 fresh source comparisons and exact elimination identities; positivity recovery is the separate general proof.')


def verify_positive_recovery():
    cases=accepted=signed_TC=rejected_signed=nonpowers=0;samples=[]
    for S in range(1,10):
        for Zstar in (3*S+1,4*S+5):
            for R in (3,5,7,9,15,27,45,81):
                for blocks in (3,4):
                    q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1);L=q**12;wide=(L-1)//2
                    assert H*(R-1)==2*J and q%2==1 and q>=3
                    power=R
                    while power%3==0:power//=3
                    for C in (1,J,q+1):
                        for V in (1,J):
                            TC=C+J-S*H;TV=V+Zstar*H
                            low=sum(q**i for i in range(8))
                            block=(1+q*q)*(C+q*V)+q*q*(J+(q*Zstar-S)*H)
                            assert block==C+q*V+q*q*TC+q**3*TV
                            raw=low+q**8*block;r=raw+wide;beta=L-r
                            lower=V+(Zstar-S)*H
                            assert raw>lower*q**11>0
                            assert raw-lower*q**11==low+C*q**8+V*q**9+(C+J)*q**10+S*H*(q**11-q**10)
                            cases+=1;nonpowers+=power!=1;signed_TC+=TC<=0
                            if beta>0:
                                assert raw<=wide and lower<=J
                                assert R-1>2*(Zstar-S)>2*S and TC>0 and TV>0
                                assert TV<=J and R-1>2*Zstar
                                accepted+=1
                                if len(samples)<3:samples.append(dict(S=S,Zstar=Zstar,R=R,blocks=blocks,C=C,V=V,TC=TC,TV=TV))
                            elif TC<=0:rejected_signed+=1
    assert accepted>0 and signed_TC>0 and rejected_signed==signed_TC
    return dict(preliminary_tuples=cases,positive_packed_slacks=accepted,
                nonpositive_formal_TC=signed_TC,nonpositive_TC_rejected_by_packed_bound=rejected_signed,
                nonpower_width_tuples=nonpowers,samples=samples,
                scope='The new pre-typing positivity implication is tested over general small fixed supports/masks and ordinary integer widths. Low fields are arbitrary positive placeholders; these tuples are not asserted to satisfy the controller or Pell system.')


def inherited_canonical_receipt():
    receipt=json.loads(Path(old.__file__).with_suffix('.json').read_text(encoding='utf-8'))
    assert receipt['status']=='PASS_SHARED_PELL_INDEX_OFFSET_109' and receipt['arithmetic']['operations']==109
    rows=[]
    for row in receipt['inherited_110_canonical']:
        assert row['transported_109_outer_residuals']==16
        rows.append(dict(x=row['x'],serial_blocks=row['serial_blocks'],counter_width=row['counter_width'],
                         packed_bits=row['packed_bits'],valuation=row['valuation'],
                         inherited_109_outer_residuals=16,transported_108_outer_residuals=14,
                         evidence='Inherited exact109 transport of frozen110 canonical coordinates; no unchanged large packed values are recomputed.',
                         source_transport='Delete TC and TV. Fresh polynomial elimination preserves the exact raw word, r, beta and every other coordinate.'))
    return rows


def verify():
    return dict(status='PASS_FACTORED_RAW_PROGRAM_BLOCK_108',arithmetic=verify_certificate(),
                positive_recovery=verify_positive_recovery(),inherited_canonical=inherited_canonical_receipt(),
                proof='../1980/EXPLORATION_FACTORED_RAW_PROGRAM_BLOCK.md',
                scope='Complete108-operation universal family by exact positive-witness elimination from109. The pre-typing signed test-word possibility is excluded by the retained packed bound. Existing universal frontier90 remains smaller.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['positive_recovery'].items() if k not in ('scope','samples')})
