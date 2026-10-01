"""One fewer polynomial operation by normalizing a native strong witness.

Accepted outer projections agree; fresh canonical auxiliaries prove
completeness.  This is neither an off-zero polynomial identity nor a
bijection between all parent positive tuples.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import pcp_uniform_affine_pair_units as parent
import binary_tag_four_tile_history as tag
import complete75_normalized_strong87 as canonical
from native_binary_input_dilation_unit179 import sort_source

execute=parent.execute
scalar=parent.parent.scalar


def rewrite(old):
    prefix=old['core_prefix'];n=lambda name:prefix+name
    rows={name:(name,op,a,b) for name,op,a,b in old['source']}
    expected={
        'L16':('*',n('f'),n('f')),
        'f_square_minus_one':('-',n('L16'),1),
        'R16':('*',n('A'),n('f_square_minus_one')),
        'ic22':('*',n('ic2'),n('ic2')),
        'L17':('*',n('R16'),n('aux_square_gap')),
    }
    assert all(rows[n(key)][1:]==value for key,value in expected.items())
    strong=(n('ic22'),n('R16'))
    assert strong in old['comparisons']
    assert old['comparisons'][-1]==(old['unit_register'],1)
    for key,consumers in [('i',{'ic2'}),('ic2',{'ic22'}),
                          ('f_square_minus_one',{'R16'}),('ic22',set()),('R16',{'L17'})]:
        assert {name for name,_,a,b in old['source'] if n(key) in (a,b)}=={n(c) for c in consumers}
    Q=n('normalized_strong_Q');N=n('f_square_minus_one')
    changes={N:(N,'-',n('L16'),Q),n('R16'):(n('R16'),'*',n('A'),Q)}
    source=[changes.get(name,(name,op,a,b)) for name,op,a,b in old['source']]
    unit=n('normalized_all_units')
    source += [(Q,'*',n('A'),n('ic22')),(unit,'*',old['unit_register'],N)]
    source=sort_source(source,old['parameters']+old['auxiliaries'])
    pairs=[pair for pair in old['comparisons'][:-1] if pair!=strong]+[(unit,1)]
    cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==old['operations']+2
    assert cc==dict(M=old['multiplications']+2,A=old['additions_subtractions'])
    assert len(pairs)==old['equations']-1
    return dict(old,source=source,comparisons=pairs,operations=len(source),
        multiplications=cc['M'],additions_subtractions=cc['A'],equations=len(pairs),
        unit_register=unit,unit_factors=old['unit_factors']+[N],parent_packet=old,
        normalized_strong_factor=N,removed_strong_comparison=strong,
        exact_degree=90*old['scale_exponent']+24,
        alternative_SOS_degree=148*old['scale_exponent']+68)


def build(maps=parent.parent.DEFAULT_MAPS,layout='auto'):
    return rewrite(parent.build(maps,layout))


def build_tag(beta=3,production='ccbbb'):
    return rewrite(tag.build(beta,production))


def polynomial_source(packet,*,include_initial_singleton=False):
    source,out=parent.polynomial_source(packet)
    if include_initial_singleton:
        beta=packet['beta']
        source += [('tag_initial_singleton','-','x',3*(1<<beta)),
                   ('tag_complete_output','*',out,'tag_initial_singleton')]
        out='tag_complete_output'
    return source,out


def lift(packet,values):
    env=execute(packet['source'],values);p=packet['core_prefix']
    return dict(values,**{p+'i':env[p+'A']*values[p+'i']})


def audit_identity(packet,values):
    old=packet['parent_packet'];p=packet['core_prefix'];n=lambda a:p+a
    env=execute(packet['source'],values)
    before=execute(old['source'],lift(packet,values))
    Delta=env[n('A')];N=env[packet['normalized_strong_factor']]
    residual=before[n('ic22')]-before[n('R16')]
    assert residual==Delta*(1-N)
    assert env[n('P17')]==before[n('P17')]+residual*env[n('aux_square_gap')]
    for name in old['unit_factors']:
        if name!=n('P17'):assert env[name]==before[name]
    pairs=old['comparisons'][:-1]
    other=[scalar(a,before)-scalar(b,before) for a,b in pairs if (a,b)!=packet['removed_strong_comparison']]
    assert other==[scalar(a,env)-scalar(b,env) for a,b in packet['comparisons'][:-1]]
    factors=[before[name] if name!=n('P17') else before[name]+residual*env[n('aux_square_gap')]
             for name in old['unit_factors']]+[N]
    product=1
    for f in factors:product*=f
    assert env[packet['unit_register']]==product
    source,out=polynomial_source(packet)
    expected=product*(1+sum(v*v for v in other))-1
    assert execute(source,values)[out]==expected
    if 'beta' in packet:
        source,out=polynomial_source(packet,include_initial_singleton=True)
        assert execute(source,values)[out]==expected*(values['x']-3*(1<<packet['beta']))


def ledger(packet):
    source,_=polynomial_source(packet);cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    old=packet['parent_packet'];oldsource,_=parent.polynomial_source(old)
    assert len(source)==len(oldsource)-1
    ans=dict(scale_exponent=packet['scale_exponent'],certificate=dict(
        operations=packet['operations'],multiplications=packet['multiplications'],
        additions_subtractions=packet['additions_subtractions'],equations=packet['equations'],
        witnesses=packet['witnesses']),polynomial=dict(operations=len(source),
        multiplications=cc['M'],additions_subtractions=cc['A'],degree=packet['exact_degree']))
    if 'beta' in packet:
        source,_=polynomial_source(packet,include_initial_singleton=True)
        cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
        ans.update(beta=packet['beta'],production=packet['production'],including_initial_singleton=dict(
            operations=len(source),multiplications=cc['M'],additions_subtractions=cc['A'],
            degree=packet['exact_degree']+1))
    return ans


def degree_audit(packet):
    t=sp.Symbol('t');names=packet['parameters']+packet['auxiliaries'];p=packet['core_prefix']
    weights={name:1+j%3 for j,name in enumerate(names)}
    weights[p+'tau_gap']=1;weights[p+'eta']=weights[p+'zeta']=1
    values={name:sp.Poly(weights[name]*t+j+1,t) for j,name in enumerate(names)}
    products={packet['unit_register']}|{row[0] for row in packet['source']
                                     if row[0].startswith(p+'history_unit_product')}
    source=[row for row in packet['source'] if row[0] not in products]
    env=execute(source,values);d=2*packet['scale_exponent']
    factors=[sp.Poly(env[name],t) for name in packet['unit_factors']]
    assert [f.degree() for f in factors]==[5*d+7,20*d+8,3*d+5,d,8*d+14]
    outer=[sp.Poly(scalar(a,env)-scalar(b,env),t) for a,b in packet['comparisons'][:-1]]
    degrees=[v.degree() for v in outer]
    assert max(degrees)==4*d-5 and degrees.count(4*d-5)==3
    top=lambda name:sp.Poly(env[p+name],t).LC()
    a,c,r,q=top('R12'),top('R10a'),top('bs_packed'),top('q')
    i,w,g,ga=map(lambda key:weights[p+key],('i','w','tau_gap','ga'))
    k=weights[p+'eta']+weights[p+'zeta'];s=2*weights[p+'odd_half']
    expected_factors=[8*ga*a*a*c,4*a**4*i*i*c**4*r*r,
                      4*w*s*s*k*(g-k)*q**3,q,-a*a*i*i*c**4]
    assert [f.LC() for f in factors]==expected_factors
    outertop=sum(v.LC()**2 for v in outer if v.degree()==4*d-5)
    assert outertop==6*r*r
    coefficient=outertop
    for f in factors:coefficient*=f.LC()
    expected=-768*ga*w*s*s*k*(g-k)*q**4*a**8*i**4*c**9*r**4
    assert coefficient==expected and coefficient
    assert sum(f.degree() for f in factors)+2*max(degrees)==packet['exact_degree']
    return dict(scale_exponent=packet['scale_exponent'],factor_degrees=[f.degree() for f in factors],
        outer_degrees=degrees,exact_degree=packet['exact_degree'],leading_coefficient_sha256=
        hashlib.sha256(hex(int(coefficient)).encode()).hexdigest(),all_five_leading_forms_checked=True,
        outer_leading_sum='6*r_top^2',highest_form=
        '-768*ga*w*s_top^2*k*(g-k)*q_top^4*a_top^8*i^4*c_top^9*r_top^4')


def verify():
    rng=random.Random(1961015)
    packets=[build(maps,layout) for maps in [((1,0,1,0),),parent.parent.DEFAULT_MAPS]
             for layout in ('contiguous','interleaved')]
    packets += [build_tag(beta,u) for beta,u in [(2,'cbb'),(3,'ccbbb'),(4,'ccbbbbb'),(10,'cbcbbbbbbb')]]
    identities=0
    for packet in packets:
        for case in range(64):
            values={name:rng.randrange(1,6) if case<32 else rng.randrange(-4,5)
                    for name in packet['parameters']+packet['auxiliaries']}
            audit_identity(packet,values);identities+=1
    signs=0
    for a in range(4):
      for f in range(4):
       for t in range(4):
        assert (f*f-((a+2)**2-1)*t*t)%4!=3;signs+=1
    canonical_cases=[canonical.canonical(A,3) for A in range(2,9)]+[canonical.canonical(2,7)]
    sample=build_tag();source,out=polynomial_source(sample,include_initial_singleton=True)
    assert ledger(sample)['including_initial_singleton']==dict(operations=196,
        multiplications=93,additions_subtractions=103,degree=1015)
    return dict(status='PASS_PCP_NORMALIZED_STRONG_HISTORY_UNITS',ledgers=[ledger(p) for p in packets],
        degree_audits=[degree_audit(p) for p in packets],
        checks=dict(complete_signed_correction_identities=identities,signed_assignments=identities//2,
                    mod4_cases=signs,canonical_auxiliary_cases=canonical_cases,
                    full_history_Pell_zeros_materialized=False),
        example=dict(parameters=sample['parameters'],auxiliaries=sample['auxiliaries'],
                     source=source,comparisons=sample['comparisons'],output=out),
        scope='Same positive outer projection as each single-kernel native-unit history parent; '
              'fresh canonical five-auxiliary extension, not a positive tuple bijection. '
              'Tag196 is an encoded-input predicate, not a universal ordinary-input bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
