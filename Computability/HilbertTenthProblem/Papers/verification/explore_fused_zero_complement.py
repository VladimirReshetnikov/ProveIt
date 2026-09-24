#!/usr/bin/env python3
"""Exact108: fuse adjacent zero/complement words using the existing q-1."""
from pathlib import Path
import json
import sympy as sp
import explore_shared_pell_index_offset as old

PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[n for n in old.OUTER_NAMES if n!='Z']
SYM={n:s for n,s in old.SYM.items() if n!='Z'}
ALIGNED=old.old.ALIGNED


def substitution():
    return {old.SYM['Z']:SYM['H']-SYM['Dzero']}


def build():
    prior,pairs,source=old.build();ops=[]
    for row in prior:
        if row[0] in ('zero_flag_sum','q2','pack_sum3','pack_product4','pack_sum4'):continue
        if row[0]=='pack_product0':ops.append(('q2','*','q','q'))
        if row[0]=='pack_product3':
            ops.extend([('zero_high','*','q2','pack_sum2'),
                        ('zero_difference','*','twice_J','Dzero'),
                        ('zero_pair','+','H','zero_difference'),
                        ('pack_sum4','+','zero_high','zero_pair')])
        else:ops.append(row)
    origins=[i for i in range(len(source)) if i!=21]
    newpairs=[pairs[i] for i in origins]
    newsource=[sp.expand(source[i].subs(substitution())) for i in origins]
    newsource[9]+=2*newsource[0]*SYM['Dzero']*SYM['q']**6
    return ops,newpairs,newsource,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==108 and counts=={'+':53,'*':55}
    assert len(pairs)==len(source)==25 and len(OUTER_NAMES+CORE_NAMES)==37
    prior=old.build()[2];sub=substitution();u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    assert sp.expand(prior[21].subs(sub))==0
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,i
        delta=2*source[0]*SYM['Dzero']*SYM['q']**6 if i==9 else 0
        assert sp.expand(polynomial-prior[origin].subs(sub)-delta)==0,i
        records.append(dict(index=i,old_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'Z','zero_flag_sum'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert ZALL>PROGRAM['hs']+4*PROGRAM['hz']
    return dict(status='PASS',operations=108,primitive_histogram=counts,
                parameters=['x'],unknown_count=37,equations=25,
                positive_unknowns=OUTER_NAMES+CORE_NAMES,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_source_identity='new_pack=old_pack[Z:=H-D]+2*q^6*D*old_q_geometry',
                exact_pair='Z+q*D=H+(q-1)*D=H+twice_J*D',
                scope='All source and primitive identities are checked. Positivity of the eliminated Z is a decoded-prefix theorem, not an assumption of the arithmetic substitution.')


def boolean(value):
    if value<0:return False
    while value:
        if value%3>1:return False
        value//=3
    return True


def verify_pair_lemma():
    cases=negative=rejected=zero=typed=nonpowers=0
    # The proof only needs q=2J+1, 0<H<=J/4 and 0<D<J.
    # Include nonpowers for the Euclidean borrow bound. Boolean testing
    # is only meaningful for the radix powers of three.
    for q in range(9,244,2):
        J=(q-1)//2
        Hvalues=sorted({1,max(1,J//8),max(1,J//4)})
        p=q
        while p%3==0:p//=3
        for H in Hvalues:
            if 4*H>J:continue
            for D in range(1,J):
                Z=H-D;pair=H+(q-1)*D
                assert pair==Z+q*D and 0<pair<q*q
                high,low=divmod(pair,q)
                if Z<0:
                    assert high==D-1 and low==q+Z and low>J
                    negative+=1
                    if p==1:
                        assert not boolean(low)
                        rejected+=1
                else:
                    assert high==D and low==Z
                    zero+=Z==0
                if p==1 and boolean(low) and boolean(high):
                    assert Z>=0 and boolean(Z) and boolean(D)
                    typed+=1
                nonpowers+=p!=1;cases+=1
    return dict(integer_pair_cases=cases,negative_formal_zero_cases=negative,
                power_radix_negative_pairs_rejected=rejected,
                zero_word_cases=zero,typed_power_pairs=typed,nonpower_cases=nonpowers,
                scope='Borrow and range checks include ordinary odd nonpower radices. Boolean conclusions are tested only at powers of three. Z=0 is deliberately accepted by this local lemma; the fixed mandatory prefix excludes it in full solutions.')


def inherited_canonical_receipt():
    receipt=json.loads(Path(old.__file__).with_suffix('.json').read_text(encoding='utf-8'))
    assert receipt['status']=='PASS_SHARED_PELL_INDEX_OFFSET_109'
    result=[]
    for row in receipt['inherited_110_canonical']:
        assert row['transported_109_outer_residuals']==16
        result.append(dict(x=row['x'],counter_width=row['counter_width'],
                           packed_bits=row['packed_bits'],valuation=row['valuation'],
                           retained_108_outer_residuals=15,
                           evidence='Inherited unchanged110/109 full canonical values. Fresh exact substitution and q-geometry identity transport all new outer equations.'))
    assert PROGRAM['edges'][0]==(0,1) and PROGRAM['zeros'][1]==1
    assert all(v==1 for u,v in PROGRAM['edges'] if u==0)
    assert PROGRAM['phases'][1]==1
    return result


def verify():
    return dict(status='PASS_FUSED_ZERO_COMPLEMENT_108',arithmetic=verify_certificate(),
                pair_lemma=verify_pair_lemma(),inherited_canonical=inherited_canonical_receipt(),
                proof='../1980/EXPLORATION_FUSED_ZERO_COMPLEMENT.md',
                scope='Complete108 universal family with full independent proof/source review and fresh verification. The established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['pair_lemma'])
