#!/usr/bin/env python3
"""Fold the two shifted AND inputs in the complete132 recoder.

Every supplied coordinate, comparison residual and full polynomial is
identical to the parent; two private additions disappear.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_input_dilation132 as parent

execute=parent.execute


def build():
    old=parent.build();rows={n:(n,op,a,b) for n,op,a,b in old['source']}
    expected={
        'Hhat':('Hhat','+','copies',1),
        'Mhat':('Mhat','+','K',1),
        'and__scaled_A':('and__scaled_A','*',16,'Hhat'),
        'and__padded_A':('and__padded_A','-','and__scaled_A',4),
        'and__scaled_B':('and__scaled_B','*',16,'Mhat'),
        'and__padded_B':('and__padded_B','-','and__scaled_B',6),
    }
    assert all(rows[n]==row for n,row in expected.items())
    for private,user in (('Hhat','and__scaled_A'),('Mhat','and__scaled_B'),
                         ('and__scaled_A','and__padded_A'),('and__scaled_B','and__padded_B')):
        assert {n for n,_,a,b in old['source'] if private in (a,b)}=={user}
        assert not any(private in pair for pair in old['comparisons'])
    changes={
        'and__scaled_A':('and__scaled_A','*',16,'copies'),
        'and__padded_A':('and__padded_A','+','and__scaled_A',12),
        'and__scaled_B':('and__scaled_B','*',16,'K'),
        'and__padded_B':('and__padded_B','+','and__scaled_B',10),
    }
    source=[changes.get(n,(n,op,a,b)) for n,op,a,b in old['source'] if n not in ('Hhat','Mhat')]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==130 and counts=={'M':67,'A':63}
    return dict(old,source=source,operations=130,multiplications=67,additions_subtractions=63,
                inline_inputs=True,removed_registers=['Hhat','Mhat'],
                changed_private_registers=['and__scaled_A','and__scaled_B'])


def source_checks():
    old=parent.build();new=build()
    os,oo=parent.sos_source(old);ns,no=parent.sos_source(new)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in ns)
    assert len(ns)==231 and counts=={'M':101,'A':130}
    assert new['parameters']==old['parameters'] and new['auxiliaries']==old['auxiliaries']
    assert new['comparisons']==old['comparisons']
    h,k=sp.symbols('h k')
    assert sp.expand(16*h+12-(16*(h+1)-4))==0
    assert sp.expand(16*k+10-(16*(k+1)-6))==0
    rng=random.Random(130233);cases=0
    for case in range(1024):
        positive=case<640
        values={n:rng.randrange(1,16) if positive else rng.randrange(-7,9)
                for n in old['parameters']+old['auxiliaries']}
        before,after=execute(os,values),execute(ns,values)
        changed=set(new['changed_private_registers'])
        assert all(after[n]==before[n] for n in after if n in before and n not in changed)
        assert parent.residuals(new,values)==parent.independent(values)
        assert after[no]==before[oo]==sum(v*v for v in parent.independent(values))
        if positive:
            assert values['x']*values['J']+1>0 and values['K']+1>0
            assert after['and__padded_A']>0 and after['and__padded_B']>0
        cases+=1
    T=sp.Symbol('T');weights={n:1+i%3 for i,n in enumerate(new['parameters']+new['auxiliaries'])}
    values={n:sp.Poly(weights[n]*T+i+1,T) for i,n in enumerate(weights)}
    a,b=execute(old['source'],values),execute(new['source'],values)
    assert all(a[left]-a[right]==b[left]-b[right] for left,right in old['comparisons'])
    residual_polys=[b[left]-b[right] for left,right in new['comparisons']]
    assert max(p.degree() for p in residual_polys)==20
    top=sum(p.LC()**2 for p in residual_polys if p.degree()==20)
    expected=weights['and__w']**4*weights['and__s']**8*weights['and__k']**4*(16*weights['q']*weights['P'])**12
    assert top==expected
    return dict(new,arbitrary_full_identity_cases=dict(positive=640,signed=384),
                polynomial=dict(operations=231,multiplications=101,additions_subtractions=130,
                                exact_degree=40,weighted_leading_coefficient=str(top)),
                parent_residuals_identical=True,full_polynomial_identical=True,
                retained_computations_identical_except_listed_private_products=True)


def outer_checks():
    rng=random.Random(130164);cases=0
    packet=build();old=parent.build()
    for case in range(384):
        n=rng.randrange(2,31);x=rng.randrange(1,1<<n)
        v=parent.outer_fixture(x,n)
        values={name:1 for name in packet['parameters']+packet['auxiliaries']};values.update(v)
        before,after=execute(old['source'],values),execute(packet['source'],values)
        assert [after[a]-after[b] for a,b in packet['comparisons'][:5]]==[0]*5
        assert after['and__padded_A']==before['and__padded_A']==16*x*v['J']+12
        assert after['and__padded_B']==before['and__padded_B']==16*v['K']+10
        assert parent.residuals(packet,values)==parent.residuals(old,values)
        cases+=1
    return dict(genuine_outer_source_substitutions=cases,full_Pell_zeros_materialized=False)


def verify():
    return dict(status='PASS_NATIVE_BINARY_INPUT_DILATION130',certificate=source_checks(),
                outer=outer_checks(),
                scope='Exactly the132 parent positive relation z=sum bit_j(x)*16^j. '
                      'Two private shifted-input additions are folded into the paid native '
                      'paddings; no witness, equation, typing or PCP interface assumption changes.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
