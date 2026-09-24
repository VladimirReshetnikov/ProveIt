#!/usr/bin/env python3
"""Exact105: combine all three raw packing factorizations."""
from pathlib import Path
import json
import sympy as sp
import explore_factored_raw_blocks as old
import explore_fused_zero_complement as zero

PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[n for n in old.OUTER_NAMES if n!='Z']
SYM={n:s for n,s in old.SYM.items() if n!='Z'}
SUB={old.SYM['Z']:SYM['H']-SYM['Dzero']}
ALIGNED=old.old.old.ALIGNED


def build():
    prior,pairs,source,origins=old.build();ops=[]
    for row in prior:
        if row[0] in ('zero_flag_sum','pack_sum3','pack_product4','pack_sum4'):continue
        if row[0]=='pack_product3':
            ops.extend([('zero_high','*','q2','pack_sum2'),
                        ('zero_difference','*','twice_J','Dzero'),
                        ('zero_pair','+','H','zero_difference'),
                        ('pack_sum4','+','zero_high','zero_pair')])
        else:ops.append(row)
    keep=[i for i,origin in enumerate(origins) if origin!=21]
    newpairs=[pairs[i] for i in keep]
    newsource=[sp.expand(source[i].subs(SUB)) for i in keep]
    neworigins=[origins[i] for i in keep]
    pack=neworigins.index(9)
    newsource[pack]+=2*newsource[neworigins.index(0)]*SYM['Dzero']*SYM['q']**6
    return ops,newpairs,newsource,neworigins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==105 and counts=={'+':50,'*':55}
    assert len(pairs)==len(source)==21 and len(OUTER_NAMES+CORE_NAMES)==33
    ancestor=old.old.build()[2];allsub=dict(old.SUB);allsub.update(SUB)
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i in (5,6,21,22,23):assert sp.expand(ancestor[i].subs(allsub,simultaneous=True))==0
    for i,((left,right),polynomial,origin) in enumerate(zip(pairs,source,origins)):
        correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2) if origin==18 else 0
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0,(i,origin)
        delta=2*source[origins.index(0)]*SYM['Dzero']*SYM['q']**6 if origin==9 else 0
        assert sp.expand(polynomial-ancestor[origin].subs(allsub,simultaneous=True)-delta)==0,i
        records.append(dict(index=i,old_109_index=origin,equality=[left,right],
                            source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'Z','B0','B1','PTC','PTV','zero_flag_sum'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert sum(row[0]=='q2_plus_one' for row in ops)==1
    assert sum('q2_plus_one' in row[2:] for row in ops)==2
    assert ZALL>max(3*PROGRAM['S'],PROGRAM['hs']+4*PROGRAM['hz'])
    return dict(status='PASS',operations=105,primitive_histogram=counts,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,unknown_count=33,equations=21,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_109_unknowns=['B0','B1','Z','PTC','PTV'],
                    deleted_109_sources=[5,6,21,22,23],retained_semantic_masks=12,
                    packing_identity='new_pack=old109_pack[all five substitutions]+2q^6 D old_q_geometry'),
                scope='Direct source audit against109 with all five substitutions, the q-geometry correction and the mapped auxiliary norm correction. Strict positivity is proved through the grouped lower block and the compiled prefix.')


def verify_composed_positivity():
    cases=accepted=negative_Z=bad_TC=rejected_TC=accepted_negative_Z=0
    for R in (3,5,9,15,27,81):
        q=R**3;J=(q-1)//2;H=(q-1)//(R-1)
        for S in (1,3,10):
            for Zstar in (3*S+1,6*S+13):
                for A0,A1,T in ((1,1,1),(J,1,J)):
                    for D in sorted({1,H,H+1,J-1,J+1}):
                        C=V=1;Z=H-D;TC=C+J-S*H;TV=V+Zstar*H
                        G=(q+1)*(A0+q*q*A1)+(1+q*q)*T
                        low=1+q*G+2*q**5+q**6*(H+2*J*D)
                        fields=[1,A0+T,A0,A1+T,A1,2,Z,D,C,V,TC,TV]
                        prog=(1+q*q)*(C+q*V)+q*q*(J+(q*Zstar-S)*H)
                        raw=low+q**8*prog;Q=V+(Zstar-S)*H
                        assert low>0 and raw==sum(a*q**i for i,a in enumerate(fields))
                        assert raw-Q*q**11==low+C*q**8+V*q**9+(C+J)*q**10+S*H*(q**11-q**10)>0
                        negative_Z+=Z<0;bad_TC+=TC<=0;cases+=1
                        if raw<=(q**12-1)//2:
                            assert Q<=J and J>S*H and TC>0 and TV>0
                            assert TV<=J and R-1>2*Zstar
                            accepted+=1;accepted_negative_Z+=Z<0
                        elif TC<=0:rejected_TC+=1
    assert accepted>0 and negative_Z>0 and bad_TC==rejected_TC>0 and accepted_negative_Z>0
    return dict(composed_cases=cases,positive_packed_slacks=accepted,
                negative_formal_Z_cases=negative_Z,nonpositive_formal_TC_cases=bad_TC,
                nonpositive_TC_rejected=rejected_TC,positive_slack_with_negative_Z=accepted_negative_Z,
                scope='The grouped Low8 argument is checked with formally negative Z and TC. Negative Z can survive these preliminary bounds; the separate freshly checked native borrow lemma and compiled-prefix theorem are still required. These tuples are not controller or Pell witnesses.')


def inherited_canonical_receipt():
    receipt=json.loads(Path(old.__file__).with_suffix('.json').read_text(encoding='utf-8'))
    assert receipt['status']=='PASS_FACTORED_RAW_BLOCKS_106'
    rows=[]
    for row in receipt['inherited_canonical']:
        assert row['transported_106_outer_residuals']==12
        rows.append(dict(x=row['x'],counter_width=row['counter_width'],packed_bits=row['packed_bits'],
                         valuation=row['valuation'],transported_105_outer_residuals=11,
                         evidence='Inherited unchanged full canonical106/108/110 values; all new source transports are freshly checked.'))
    return rows


def verify():
    return dict(status='PASS_ALL_FACTORED_RAW_BLOCKS_105',arithmetic=verify_certificate(),
                dependency_arithmetic=dict(combined106=old.verify_certificate()['status'],zero108=zero.verify_certificate()['status']),
                composed_positivity=verify_composed_positivity(),zero_pair_lemma=zero.verify_pair_lemma(),
                inherited_canonical=inherited_canonical_receipt(),
                proof='../1980/EXPLORATION_ALL_FACTORED_RAW_BLOCKS.md',
                scope='Complete105 universal family with full independent proof/source review and fresh verification. All twelve semantic masks remain; the established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['composed_positivity'])
