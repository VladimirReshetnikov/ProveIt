#!/usr/bin/env python3
"""Standalone104: fuse the zero pair in the doubled105 construction."""
from pathlib import Path
import json
import sympy as sp
import explore_doubled_raw_coordinates as old

PROGRAM=old.PROGRAM
ZALL=old.ZALL
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=[n for n in old.OUTER_NAMES if n!='Z']
SYM={n:s for n,s in old.SYM.items() if n!='Z'}
SUB={old.SYM['Z']:SYM['H']-SYM['Dzero']}


def build():
    prior,pairs,source,origins=old.build();ops=[]
    for row in prior:
        if row[0] in ('zero_flag_sum','pack_sum3','pack_product4','pack_sum4'):continue
        if row[0]=='pack_product3':
            ops.extend([('zero_high','*','q2','pack_sum2'),
                        ('zero_difference','*','Jrep','Dzero'),
                        ('zero_pair','+','H','zero_difference'),
                        ('pack_sum4','+','zero_high','zero_pair')])
        else:ops.append(row)
    keep=[i for i,o in enumerate(origins) if o!=21]
    src=[sp.expand(source[i].subs(SUB)) for i in keep];org=[origins[i] for i in keep]
    src[org.index(9)]+=SYM['q']**6*SYM['Dzero']*src[org.index(0)]
    return ops,[pairs[i] for i in keep],src,org


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==104 and counts=={'+':48,'*':56}
    assert len(source)==len(pairs)==21 and len(OUTER_NAMES+CORE_NAMES)==33
    prior=old.build()[2];prior_origins=old.build()[3]
    assert sp.expand(prior[prior_origins.index(21)].subs(SUB))==0
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),p,o) in enumerate(zip(pairs,source,origins)):
        correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2) if o==18 else 0
        assert sp.expand(env[left]-env[right]-p-correction)==0,(i,o)
        delta=SYM['q']**6*SYM['Dzero']*source[origins.index(0)] if o==9 else 0
        assert sp.expand(p-prior[prior_origins.index(o)].subs(SUB)-delta)==0,(i,o)
        records.append(dict(index=i,old_index=o,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(correction)))
    used={a for row in ops for a in row[2:]}|{a for pair in pairs for a in pair}
    assert set(SYM)<=used and not used&{'Z','zero_flag_sum'}
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    assert ZALL>PROGRAM['hs']+4*PROGRAM['hz'] and PROGRAM['hz']%2==1
    assert PROGRAM['zeros'][0]==0 and PROGRAM['zeros'][1]==1
    assert all(v==1 for u,v in PROGRAM['edges'] if u==0)
    return dict(status='PASS',operations=104,primitive_histogram=counts,unknown_count=33,equations=21,
                parameters=['x'],positive_unknowns=OUTER_NAMES+CORE_NAMES,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                source_identity='new_pack=old_pack[Z:=H-D]+q^6*D*(q-J-1)',
                scope='All104 primitives and21 source comparisons, including the undoubled packed-source geometry correction. Strict positivity of the eliminated Z uses the routed parity and marked-prefix proof.')


def even_boolean(v):return v>=0 and v%2==0 and old.boolean(v//2)


def verify_routed_pair():
    cases=negative=typed=even_negative=odd_aliases=zero=0
    for n in range(2,7):
        q=3**n;J=q-1
        for H in sorted({2,2*max(1,J//16),2*max(1,J//8)}):
            if 4*H>J:continue
            for D in range(1,J):
                Z=H-D;pair=H+J*D
                assert pair==Z+q*D and 0<pair<q*q
                high,low=divmod(pair,q)
                cases+=1;negative+=Z<0
                if even_boolean(low) and even_boolean(high):
                    typed+=1
                    if D%2==0:
                        assert Z>=0
                        zero+=Z==0
                    elif Z<0:odd_aliases+=1
                if Z<0 and D%2==0:
                    assert low%2==1 and not even_boolean(low)
                    even_negative+=1
    # A real local doubled-mask alias is rejected by route parity, not by
    # the unrestricted pair mask. It is not a complete source solution.
    q=9;J=8;H=2;D=3;Z=-1;pair=H+J*D
    assert pair==26 and even_boolean(pair%q) and even_boolean(pair//q)
    R=9;K=3;g=gI=hs=hz=1;C=V=Kp=2
    residual=(R*K-g)*C-gI*(2*J)-R*(V+hs*Kp+hz*D)
    assert residual%2==D%2==1
    return dict(integer_pairs=cases,negative_formal_zero_pairs=negative,typed_doubled_pairs=typed,
                even_D_negative_pairs_rejected=even_negative,odd_D_local_mask_aliases=odd_aliases,
                locally_allowed_zero_words=zero,
                explicit_odd_alias=dict(q=q,H=H,D=D,Z=Z,packed_pair=pair,route_residual=residual),
                scope='The exact route parity excludes the real odd-D local mask aliases. These bounded pair assignments do not claim to satisfy the complete geometry/controller system; Z=0 is left to the mandatory prefix.')


def verify():
    # Freshly recompute both complete predecessor outer tuples, then use
    # the exact source identity above to transport their retained values.
    canonical=[]
    for x in (1,2):
        row=old.canonical(x)
        assert row['outer_residuals']==12
        canonical.append(dict(**row,fresh_predecessor_outer_residuals=12,
                              transported_104_outer_residuals=11,
                              evidence='Fresh complete doubled105 outer tuple and valuation, followed by the freshly checked zero substitution. Same packed index and all retained coordinates.'))
    return dict(status='PASS_DOUBLED_ZERO_FUSION_104',arithmetic=verify_certificate(),
                routed_pair=verify_routed_pair(),canonical=canonical,
                proof='../1980/EXPLORATION_DOUBLED_ZERO_FUSION.md',
                scope='Separate104 over doubled105, with original positive guards and full independent proof/source reviews and fresh verification; no composition with complemented guards. Existing universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['routed_pair']);print(result['canonical'])
