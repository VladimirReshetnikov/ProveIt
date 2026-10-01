"""Compute the history scale from its paid bound:257 operations, degree1384.

The old range-unit equation is exchanged for the signed repunit equation.
The new sign is excluded before chronological decoding. Positive completeness
uses beta_new=beta_old+1; arbitrary off-zero polynomials are not identical.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from math import prod
from pathlib import Path
import random
import neary_woods_universal_offset258 as parent

compiler,execute=parent.compiler,parent.execute
polynomial_source,degree_bound=parent.polynomial_source,parent.degree_bound
SCALE='hist__P__10';BOUND='hist__global_lhs__15';PRODUCT='hist__P_product__9'
UNIT='history_global_unit';SLACK='hist__global_bound';SUM='hist__global_sum__14'


def guard_parent(old):
    assert old.get('program_offset_minus_one') and not old.get('history_scale_from_bound')
    expected=parent.rewrite(old['offset_parent'])
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','fixed_numerals','width','interfaces','public_registers',
                'fusion_interfaces','projected_coordinates','normalized_prefixes',
                'positive_scale_prefixes','bound_is_program_E','operations',
                'multiplications','additions_subtractions','equations','witnesses',
                'initial_register','initial_value_expression','lower_unit_semantic_hypothesis'):
        assert old.get(key)==expected.get(key),key
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[SCALE]==('+',PRODUCT,1)
    assert rows[BOUND]==('+',SLACK,SUM)
    assert rows[UNIT]==('-',SCALE,BOUND)
    assert rows[PRODUCT]==('*','hist__Bm1__8','hist__J__7')
    assert {n for n,_,a,b in old['source'] if BOUND in (a,b)}=={UNIT}
    assert {n for n,_,a,b in old['source'] if SLACK in (a,b)}=={BOUND}
    for key in ('interfaces','public_registers','fusion_interfaces','projected_coordinates','comparisons','unit_factors'):
        assert BOUND not in parent.parent.parent.parent.parent.leaves(old.get(key,{}))


def rewrite(old):
    guard_parent(old)
    source=[]
    for n,op,a,b in old['source']:
        if n==BOUND:continue
        if n==SCALE:op,a,b='+',SLACK,SUM
        if n==UNIT:op,a,b='-',SCALE,PRODUCT
        source.append((n,op,a,b))
    result=dict(old,source=source,operations=old['operations']-1,
        additions_subtractions=old['additions_subtractions']-1,
        history_scale_parent=old,history_scale_from_bound=True,
        history_scale_definition='P=H_U+H_V+ZUhat0+ZVhat0+ZVhat1+global_bound',
        history_repunit_unit='P-(B_history-1)*J_history',
        historical_global_bound_register=BOUND,
        identical_complete_polynomial=False,affine_complete_polynomial_identity=False,
        identical_positive_zero_set=False,positive_zero_bijection='global_bound_new=global_bound_parent+1 on inherited valid program/input slices',
        accepted_input_equivalence='Inherited valid program/input slices; the program-offset-minus-one recipe is unchanged',
        history_scale_completeness_map='global_bound_new=global_bound_parent+1 at parent zeros')
    compiler.check_source(result)
    return result


def build(parent_operations=260,*,merge_bound=True,witnesses=None):
    return rewrite(parent.build(parent_operations,merge_bound=merge_bound,witnesses=witnesses))


def project_from_parent(packet,values):
    result=dict(values);result[SLACK]+=1;return result


def conditional_lift_to_parent(packet,values):
    """Algebraic lift on the +1 repunit locus; positivity is not asserted."""
    result=dict(values);result[SLACK]-=1;return result


def ledger(packet):
    source,out=polynomial_source(packet);old=packet['history_scale_parent'];before,_=polynomial_source(old)
    parent.parent.parent.parent.parent.parent.loader.source_closure(source,out)
    c=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==len(before)-1
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    d=degree_bound(packet)
    return dict(parent_polynomial_operations=len(before),bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['M'],additions_subtractions=c['A'],
            degree_upper_bound=d['degree_upper_bound'],exact_degree_claimed=False),degree=d)


def overridden_execute(source,values,overrides):
    env=dict(values)
    def at(v):return env[v] if isinstance(v,str) else v
    for n,op,a,b in source:
        x,y=at(a),at(b)
        env[n]=overrides[n] if n in overrides else x+y if op=='+' else x-y if op=='-' else x*y
    return env


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['history_scale_parent'];ns,no=polynomial_source(packet);bs,bo=polynomial_source(old)
    positives=0
    for case in range(cases):
        draw=lambda:rng.randrange(1,5) if case<cases//2 else rng.randrange(-3,4)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']};fixed={n:draw() for n in compiler.NUMERALS}
        if case<cases//2:values['hist__Shat0']+=4
        sm=compiler.materialize(ns,fixed);bm=compiler.materialize(bs,fixed)
        en=execute(sm,values)
        desired=sum(values[n] for n in ('hist__H_U','hist__H_V','hist__ZUhat0','hist__ZVhat0','hist__ZVhat1',SLACK))
        assert en[SCALE]==desired and en[UNIT]==desired-en[PRODUCT]
        oracle=overridden_execute(bm,values,{SCALE:desired,UNIT:desired-en[PRODUCT]})
        assert all(en[n]==oracle[n] for n,_,_,_ in old['source'] if n!=BOUND)
        groups=[prod(en[packet['unit_factors'][j]] for j in g) for g in packet['factor_partition']]
        assert groups==[en[n] for n in packet['group_products']]
        # Any ordinary strong residuals are retained; group comparisons are last.
        groupregs=set(packet['group_products'])
        ordinary=[en[a]-en[b] if isinstance(a,str) and isinstance(b,str) else
                  (en[a] if isinstance(a,str) else a)-(en[b] if isinstance(b,str) else b)
                  for a,b in packet['comparisons'] if a not in groupregs]
        anchor=packet['partition_anchor']
        sums=sum(r*r for r in ordinary)+sum((g-1)**2 for i,g in enumerate(groups) if i!=anchor)
        expected=sums if anchor is None else groups[anchor]*(1+sums)-1
        assert en[no]==oracle[bo]==expected
        # Exact parent identity on the signed algebraic +1 repunit locus.
        probe=execute(bm,values);vv=dict(values);vv[SLACK]=probe[PRODUCT]-probe[SUM]+1
        lifted=conditional_lift_to_parent(packet,vv)
        a=execute(bm,lifted);b=execute(sm,vv)
        assert b[UNIT]==a[UNIT]==1
        assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n!=BOUND)
        assert a[bo]==b[no] and project_from_parent(packet,lifted)==vv
        if case<cases//2:
            assert min(vv.values())>0 and min(lifted.values())>0;positives+=1
    return dict(complete_scale_substitution_outputs=cases,conditional_parent_output_identities=cases,
        signed_assignments=cases//2,positive_parent_extensions=positives)


def packed_words(P,Bh,D,S,HU,HV,Z):
    J=sum(S);rep=lambda n:sum(P**i for i in range(n))
    sel=sum(s*P**i for i,s in enumerate(S));hb=HU+P*HV+P*P*HV
    zb=sum(z*P**i for i,z in enumerate(Z));group=(S[1]+S[2])+P*S[0]+P*P*S[1]
    mb=(Bh-1)*group;rh=HU+P*HV;rm=(D-1)*J*(P+1)
    H=hb+P**3*sel+P**7*rh+Bh*P**9
    M=mb+P**3*J*rep(4)+P**7*rm+(Bh-1)*P**9
    A=zb+P**3*sel+P**7*rh
    return H,M,A,mb,P**3*J*rep(4),P**7*rm


def domain_audit():
    rng=random.Random(257135);cases=negative=nondyadic=0
    for D in range(4,20):
      for c in (4,8,16):
       Bh=c*D
       for J in (1,2,3,5,11):
        for sign in (-1,1):
         P=(Bh-1)*J+sign
         for _ in range(4):
          S=[0]*4
          for _ in range(J):S[rng.randrange(4)]+=1
          # Positive hats and slack summing exactly P.
          cuts=sorted(rng.sample(range(1,P),5));parts=[b-a for a,b in zip([0]+cuts,cuts+[P])]
          HU,HV,*rest=parts;Z=[z-1 for z in rest[:3]]
          H,M,A,mb,cm,rm=packed_words(P,Bh,D,S,HU,HV,Z)
          assert J>=1 and Bh<=P+2 and J<=P//6
          assert H>=A and M>A and P**11-H-M+A>=2
          assert H<2*P**10 and M<2*P**10
          assert H+M-A<3*P**10
          assert H%P**9<P**9 and A<P**9
          assert mb+cm<P**7 and rm+mb+cm<P**9
          assert H//P**9==Bh and M//P**9==Bh-1
          cases+=1;negative+=sign<0;nondyadic+=bool(P&(P-1))
    mersenne=modular=0
    for b in range(3,17):
      for s in range(1,257):
       assert (2**s+1)%(2**b-1)!=0;mersenne+=1
    for s in range(3,13):
      P=1<<s
      for Bh in range(16,P+3,4):
       if (P+1)%(Bh-1):continue
       J=(P+1)//(Bh-1)
       assert J%4==3 and J>=3 and Bh<P and Bh&(Bh-1)
       modular+=1
    return dict(weak_repunit_pretyping_cases=cases,negative_units=negative,nondyadic_scales=nondyadic,
        dyadic_negative_repunit_exclusions=mersenne,possible_negative_divisor_cases=modular,
        scope='Algebraic packed fields and exact modular obstructions; no complete native Pell tuples.')


def guards_audit():
    p=parent.build();bad=[]
    for name in (BOUND,SLACK):
        v=copy.deepcopy(p);v['source'].append(('outside_consumer_'+name,'+',name,1));bad.append(v)
    for key in ('public_registers','fusion_interfaces'):
        v=copy.deepcopy(p);v[key]=[BOUND];bad.append(v)
    v=copy.deepcopy(p);v['source']=[(n,'-',a,b) if n==PRODUCT else (n,op,a,b) for n,op,a,b in v['source']];bad.append(v)
    for v in bad:
        try:rewrite(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=len(bad))


def verify():
    records=[];selected=[];seen=set();engine=parent.parent.parent.parent.parent.parent
    for interface in (False,True):
      for n in engine.NORMALIZATIONS:
       for s in engine.SCALE_OPTIONS:
        base=engine.build_base(n,s,interface)
        p265=parent.parent.parent.parent.parent.rewrite(engine.factored.rewrite(base))
        p263=parent.parent.parent.parent.rewrite(p265)
        p260=parent.parent.parent.rewrite(p263)
        p259=parent.parent.rewrite(p260)
        old=parent.rewrite(p259);packet=rewrite(old)
        records.append(dict(ledger(packet),audit=audit(packet,257000+len(records))))
      for w in (None,43,44,45):
       for plan in engine.factored_frontier(w):
        old=parent.build(plan['polynomial']['operations']-9,merge_bound=interface,witnesses=w)
        key=(interface,tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
        if key in seen:continue
        seen.add(key);packet=rewrite(old);rec=ledger(packet)
        records.append(dict(rec,audit=audit(packet,2571000+len(records))))
        source,out=polynomial_source(packet);encoded=compiler.encode_source(source)
        selected.append(dict(rec,source=encoded,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=257,multiplications=133,additions_subtractions=124,degree_upper_bound=1384,exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_HISTORY_SCALE257',default=default,ledgers=records,selected_sources=selected,
        ledger_count=len(records),complete_scale_substitution_outputs=8*len(records),conditional_parent_output_identities=8*len(records),
        signed_assignments=4*len(records),positive_parent_extensions=4*len(records),domains=domain_audit(),guards=guards_audit(),
        scope='Positive-zero bijection by the global-bound shift on inherited valid program/input slices. Signed repunit excluded before chronology; no arbitrary off-zero polynomial identity or unrestricted positive-tuple claim.')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default'])
