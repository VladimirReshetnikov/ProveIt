"""Factor the computed four-field native index, saving four additions.

The final polynomial is identical over all supplied integer assignments;
only private field/packing arithmetic is replaced.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_unsquared_outer_product as six_parent
import group_projective_computed_checksum_field as four_parent
import group_projective_index_unit as index

execute=six_parent.execute
residuals=six_parent.residuals


def rewrite(old):
    private={
        'computed_input_F1': {'selection__bs_p3'},
        'computed_input_F2': {'computed_checksum_F0','selection__bs_p1'},
        'selection__bs_Q': {'selection__shared_sum02'},
        'selection__shared_sum02': {'computed_checksum_F0'},
        'computed_checksum_F0': {'selection__bs_packed'},
        'selection__bs_p0': {'selection__bs_p1'},
        'selection__bs_p1': {'selection__bs_p2'},
        'selection__bs_p2': {'selection__bs_p3'},
        'selection__bs_p3': {'selection__bs_p4'},
        'selection__bs_p4': {'selection__bs_packed'},
    }
    rows={row[0]:row for row in old['source']}
    expected=[
        ('computed_input_F1','-','selection__padded_A','selection__F3'),
        ('computed_input_F2','-','selection__padded_B','selection__F3'),
        ('selection__bs_Q','-','selection__q','selection__padded_A'),
        ('selection__shared_sum02','-','selection__bs_Q',1),
        ('computed_checksum_F0','-','selection__shared_sum02','computed_input_F2'),
        ('selection__bs_p0','*','selection__q','selection__F3'),
        ('selection__bs_p1','+','computed_input_F2','selection__bs_p0'),
        ('selection__bs_p2','*','selection__q','selection__bs_p1'),
        ('selection__bs_p3','+','computed_input_F1','selection__bs_p2'),
        ('selection__bs_p4','*','selection__q','selection__bs_p3'),
        ('selection__bs_packed','+','computed_checksum_F0','selection__bs_p4'),
        ('selection__padded_A','+','selection__scaled_A',12),
        ('selection__padded_B','+','selection__scaled_B',10),
    ]
    assert all(rows[row[0]]==row for row in expected)
    consumers={n:set() for n in private}
    for name,_,a,b in old['source']:
        for v in (a,b):
            if v in consumers:consumers[v].add(name)
    assert consumers==private
    assert not any(v in private for pair in old['comparisons'] for v in pair)
    # The old padded_A can be changed by one because all its consumers
    # belong to this private fragment. No physical port comparison remains.
    assert {n for n,_,a,b in old['source'] if 'selection__padded_A' in (a,b)}=={'computed_input_F1','selection__bs_Q'}
    assert not any('selection__padded_A' in pair for pair in old['comparisons'])
    removed=set(private)|{'selection__bs_packed'}
    source=[(n,op,a,13) if n=='selection__padded_A' else (n,op,a,b)
            for n,op,a,b in old['source'] if n not in removed]
    source += [
        ('packed_q_minus','-','selection__q',1),
        ('packed_q_plus','+','selection__q',1),
        ('packed_z_product','*','packed_q_minus','selection__F3'),
        ('packed_middle_sum','+','selection__padded_B','packed_z_product'),
        ('packed_middle_product','*','packed_q_plus','packed_middle_sum'),
        ('packed_top_sum','+','selection__padded_A','packed_middle_product'),
        ('selection__bs_packed','*','packed_q_minus','packed_top_sum'),
    ]
    source=index.parent.sort_source(source,{'x',*old['auxiliaries']})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert counts=={'M':old['multiplications'],'A':old['additions_subtractions']-4}
    return dict(old,source=source,operations=len(source),multiplications=counts['M'],
                additions_subtractions=counts['A'],factored_native_index=True,
                removed_private_index_registers=sorted(private),
                audited_private_consumers={n:sorted(v) for n,v in consumers.items()})


def build(codes,alpha=24,beta=12,variant='six',controller_mask=False,compute_length=False):
    if variant=='six':old=six_parent.build(codes,alpha,beta,controller_mask,compute_length)
    else:
        assert variant=='four'
        old=four_parent.build(codes,alpha,beta,'four',controller_mask,compute_length)
    return rewrite(old)


def polynomial_source(packet):
    return (six_parent if packet['variant']=='six' else four_parent).polynomial_source(packet)


def former_sos_source(packet):return four_parent.polynomial_source(packet)


def degree_top(packet,w):
    return (six_parent if packet['variant']=='six' else four_parent).degree_top(packet,w)


def symbolic_identity():
    q,A,B,Z=sp.symbols('q A B Z')
    f1=A-Z;f2=B-Z;f0=q-f1-f2-Z-1
    old=f0+q*f1+q*q*f2+q**3*Z
    new=(q-1)*(A+1+(q+1)*(B+(q-1)*Z))
    assert sp.expand(old-new)==0
    return dict(identity='F0+q*F1+q^2*F2+q^3*F3=(q-1)*(A+1+(q+1)*(B+(q-1)*F3))',
                substitutions='F1=A-F3; F2=B-F3; F0=q-F1-F2-F3-1',
                unconditionally_over_integers=True)


def verify():
    identity=symbolic_identity();rng=random.Random(2832376)
    records=[];cases=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for variant in ('four','six'):
       for reuse in (False,True):
        if reuse and four_parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=(six_parent.build(codes,controller_mask=reuse,compute_length=comp) if variant=='six'
                 else four_parent.build(codes,variant='four',controller_mask=reuse,compute_length=comp))
            packet=rewrite(old);source,out=polynomial_source(packet);prior,prior_out=polynomial_source(old)
            assert packet['comparisons']==old['comparisons'] and packet['auxiliaries']==old['auxiliaries']
            assert len(source)==len(prior)-4
            for case in range(64):
                z={n:rng.randrange(1,9) if case<48 else rng.randrange(-5,6)
                   for n in packet['parameters']+packet['auxiliaries']}
                env=execute(source,z);before=execute(prior,z)
                assert env['selection__padded_A']==before['selection__padded_A']+1
                assert env['selection__bs_packed']==before['selection__bs_packed']
                assert residuals(packet,env)==residuals(old,before)
                assert env[out]==before[prior_out]
                assert all(env[n]==before[n] for n,_,_,_ in packet['source']
                           if n in before and n!='selection__padded_A')
                cases+=1
            w={n:1+i%3 for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
            w['selection__tau_gap']=1
            # Exact equality of the entire output polynomial proves inherited
            # degrees, without another expansion of unchanged parent factors.
            degree=degree_top(packet,w)[0]
            assert degree==degree_top(old,w)[0]
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            m,h,p=packet['m'],packet['h'],packet['projection_additions'];flow=packet['flow']['operations']
            C=3*m+3*h+p+185+flow-3*min(h,3)-reuse
            assert packet['operations']==C-1
            assert len(source)==C+(28 if variant=='six' else 34)-3*comp
            records.append(dict(m=m,variant=variant,controller_mask=reuse,compute_length=comp,
                certificate_operations=packet['operations'],certificate_M=packet['multiplications'],
                certificate_A=packet['additions_subtractions'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                degree_justification='Exact same complete polynomial as the parent by symbolic index identity and audited private consumers.'))
            if m==16 and variant=='six' and reuse and comp:
                example=dict(packet,polynomial_source=source,polynomial_output=out)
                assert (packet['operations'],len(source),degree)==(257,283,2376)
    return dict(status='PASS_GROUP_PROJECTIVE_FACTORED_NATIVE_INDEX',identity=identity,
                records=records,source_example=example,
                complete_register_residual_and_polynomial_identities=cases,
                signed_assignments=cases//4,
                scope='Four literal additions removed. Entire integer output polynomial, positive witnesses, comparisons and ordinary input are identical to the parent; no new universal numerical alphabet is instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
