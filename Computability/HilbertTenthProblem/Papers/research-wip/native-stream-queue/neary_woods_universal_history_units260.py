"""Proved history units in the complete U9 polynomial: 260 operations.

Upper transport preserves positive tuples. The global unit uses the positive
zero bijection beta_parent=beta_new+1. Off-zero outputs obey corrections.
"""
import argparse
from collections import Counter
import copy
import hashlib
from itertools import product
import json
from pathlib import Path
import random

import neary_woods_universal_mask_unit263 as parent

compiler, execute = parent.compiler, parent.execute
polynomial_source, degree_bound = parent.polynomial_source, parent.degree_bound
UNITS = dict(upper='history_upper_unit', global_bound='history_global_unit')
PAIRS = dict(upper=('hist__U_lhs__37', 'hist__U_rhs__41'),
             global_bound=('hist__global_lhs__15', 'hist__P__10'))
SLACK = 'hist__global_bound'
MODES = dict(upper=('upper',), global_bound=('global_bound',),
             both=('upper', 'global_bound'))
SAVINGS = dict(upper=2, global_bound=1, both=3)


def guard_parent(old):
    assert old.get('mask_repunit_as_unit') and not old.get('history_unit_modes')
    ancestor = old['mask_unit_parent']
    parent.guard_parent(ancestor)
    expected = parent.rewrite(ancestor, group=old['mask_unit_group'])
    for key in ('source', 'comparisons', 'parameters', 'auxiliaries', 'unit_factors',
                'unit_register', 'unit_product', 'factor_partition', 'partition_anchor',
                'group_products', 'fixed_numerals', 'width', 'interfaces',
                'public_registers', 'fusion_interfaces', 'projected_coordinates',
                'normalized_prefixes', 'positive_scale_prefixes', 'bound_is_program_E',
                'operations', 'multiplications', 'additions_subtractions', 'equations', 'witnesses'):
        assert old.get(key) == expected.get(key), key
    rows = {n:(op,a,b) for n,op,a,b in old['source']}
    assert rows['hist__U_lhs__37'] == ('+', 'hist__U_update__36', 1)
    assert rows['hist__U_update__36'] == ('*', 'hist__B__3', 'hist__linear_constant__168')
    assert rows['hist__U_rhs__41'] == ('+', 'hist__H_U', 'hist__U_terminal__40')
    assert rows['hist__global_lhs__15'] == ('+', SLACK, 'hist__global_sum__14')
    assert {n for n,_,a,b in old['source'] if SLACK in (a,b)} == {'hist__global_lhs__15'}
    for pair in PAIRS.values(): assert old['comparisons'].count(pair) == 1
    assert not any('hist__U_lhs__37' in (a,b) for _,_,a,b in old['source'])
    for key in ('unit_factors','group_products','interfaces','public_registers',
                'fusion_interfaces','projected_coordinates'):
        assert 'hist__U_lhs__37' not in parent.parent.leaves(old.get(key, {})), key
    known = {n for n,_,_,_ in old['source']} | set(old['parameters']+old['auxiliaries'])
    assert not set(UNITS.values()) & known
    assert not any(n.startswith('history_unit_product_') for n in known)


def _rewrite(old, mode, groups):
    kinds = MODES[mode]
    assert len(groups) == len(kinds)
    assert all(type(j) is int and 0 <= j < len(old['group_products']) for j in groups)
    removed = {'hist__U_lhs__37'} if 'upper' in kinds else set()
    source = [row for row in old['source'] if row[0] not in removed]
    products = list(old['group_products'])
    partition = list(map(list, old['factor_partition']))
    factors = list(old['unit_factors'])
    for index,(kind,group) in enumerate(zip(kinds,groups)):
        unit = UNITS[kind]
        a,b = ('hist__U_rhs__41','hist__U_update__36') if kind=='upper' else ('hist__P__10','hist__global_lhs__15')
        name = f'history_unit_product_{index}'
        source += [(unit,'-',a,b),(name,'*',products[group],unit)]
        products[group]=name
        partition[group].append(len(factors)); factors.append(unit)
    aliases = dict(zip(old['group_products'],products))
    pairs = [(aliases.get(a,a),b) for a,b in old['comparisons']
             if (a,b) not in {PAIRS[k] for k in kinds}]
    count=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    packet=dict(old, source=source, comparisons=pairs, unit_factors=factors,
        group_products=products, factor_partition=partition,
        unit_register=aliases.get(old['unit_register'],old['unit_register']),
        operations=len(source), equations=len(pairs), multiplications=count['M'],
        additions_subtractions=count['A'], history_unit_modes=kinds,
        history_unit_mode=mode, history_unit_groups=tuple(groups), history_unit_parent=old,
        history_unit_erased_registers=sorted(removed),
        identical_complete_polynomial=False, identical_positive_coordinates=True,
        identical_positive_zero_set=(mode=='upper'),
        positive_zero_bijection='beta_parent=beta_new+1' if 'global_bound' in kinds else 'identity')
    assert len(source)==old['operations']+len(kinds)+int('global_bound' in kinds)
    assert count['M']==old['multiplications']+len(kinds)
    assert count['A']==old['additions_subtractions']+int('global_bound' in kinds)
    compiler.check_source(packet)
    return packet


def rewrite(old, *, mode='both', groups=None):
    assert mode in MODES
    guard_parent(old)
    if groups is not None: return _rewrite(old,mode,tuple(groups))
    candidates = [_rewrite(old,mode,g) for g in product(range(len(old['group_products'])),repeat=len(MODES[mode]))]
    return min(candidates,key=lambda p:(degree_bound(p)['degree_upper_bound'],p['history_unit_groups']))


def build(operations=None, *, merge_bound=True, witnesses=None, mode='both'):
    cost=263 if operations is None else operations+SAVINGS[mode]
    return rewrite(parent.build(cost,merge_bound=merge_bound,witnesses=witnesses),mode=mode)


def lift_to_parent(packet, values):
    result=dict(values)
    if 'global_bound' in packet['history_unit_modes']: result[SLACK]+=1
    return result


def project_from_parent(packet, values):
    result=dict(values)
    if 'global_bound' in packet['history_unit_modes']: result[SLACK]-=1
    return result


def ledger(packet):
    old=packet['history_unit_parent']
    source,output=polynomial_source(packet)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    parent.parent.parent.loader.source_closure(source,output)
    assert len(source)==len(polynomial_source(old)[0])-SAVINGS[packet['history_unit_mode']]
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['witnesses']==len(packet['auxiliaries'])
    bound=degree_bound(packet)
    return dict(mode=packet['history_unit_mode'], groups=packet['history_unit_groups'],
        normalized_prefixes=packet['normalized_prefixes'],
        positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        bound_is_program_E=packet['bound_is_program_E'],
        factor_partition=packet['factor_partition'], partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
                        degree_upper_bound=bound['degree_upper_bound'],exact_degree_claimed=False),
        new_factor_degrees={UNITS[k]:bound['factor_degree_bounds'][UNITS[k]] for k in packet['history_unit_modes']})


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['history_unit_parent']
    before_source,before_output=polynomial_source(old)
    after_source,after_output=polynomial_source(packet)
    kinds=packet['history_unit_modes'];anchor=old['partition_anchor']
    for case in range(cases):
        draw=lambda:rng.randrange(1,5) if case<cases//2 else rng.randrange(-3,4)
        fixed={n:draw() for n in compiler.NUMERALS}
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        lifted=lift_to_parent(packet,values)
        assert project_from_parent(packet,lifted)==values
        a=execute(compiler.materialize(before_source,fixed),lifted)
        b=execute(compiler.materialize(after_source,fixed),values)
        changed=set(packet['history_unit_erased_registers'])
        if 'global_bound' in kinds:changed.add('hist__global_lhs__15')
        assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n not in changed)
        modifiers=[1]*len(old['group_products']);removed_squared=0
        for kind,group in zip(kinds,packet['history_unit_groups']):
            left,right=PAIRS[kind];residual=a[left]-a[right]
            assert b[UNITS[kind]]==1-residual
            modifiers[group]*=b[UNITS[kind]];removed_squared+=residual**2
        G=[a[n] for n in old['group_products']]
        for reg,group,modifier,g in zip(packet['group_products'],packet['factor_partition'],modifiers,G):
            actual=1
            for j in group:actual*=b[packet['unit_factors'][j]]
            assert b[reg]==actual==g*modifier
        if anchor is None:
            correction=sum((g*m-1)**2-(g-1)**2 for g,m in zip(G,modifiers))
            expected=a[before_output]-removed_squared+correction
        else:
            correction=sum((G[j]*modifiers[j]-1)**2-(G[j]-1)**2 for j in range(len(G)) if j!=anchor)
            multiplier=modifiers[anchor]
            expected=multiplier*(a[before_output]+1)+multiplier*G[anchor]*(correction-removed_squared)-1
        assert b[after_output]==expected
    return dict(complete_corrected_output_and_register_cases=cases,signed_cases=cases//2)


def elementary_audit():
    population=upper=slack=0
    for width in range(3,11):
      for logQ in range(2,9):
       b=width-1+logQ;B=1<<b
       for n in range(1,9):
        J=sum(B**j for j in range(n));R=((1<<width)-1)*J
        assert R.bit_count()==width*n and (R-2).bit_count()==width*n-1
        assert pow(2,width*n-1,(1<<width)-1)!=(1%((1<<width)-1))
        population+=1
    for K in (8,16,64):
      for D in (4,8,16):
       B=K*D
       for digit in range(D):
        assert digit!=(B-1)
        for sign in (-1,1):
            assert ((digit-sign)%B==0)==(digit==1 and sign==1)
        upper+=1
       for n in range(1,5):
        J=sum(B**i for i in range(n));P=B**n
        # Maximal range digits and all possible disjoint class splits.
        HU=HV=(D-1)*J
        for ZU,ZV0,ZV1 in ((0,0,0),(HU,HV,0),(HU,0,HV)):
            beta=P-HU-HV-ZU-ZV0-ZV1-3
            assert beta>=((K-4)*D+3)*J-2>=17
            assert beta-1>0;slack+=1
    return dict(negative_geometry_population_and_loader_cases=population,
                upper_unit_low_digit_cases=upper,typed_global_slack_cases=slack)


def outer_margin_audit():
    packet=build();rng=random.Random(260171);count=negative_mask=negative_global=0
    for D in (3,4,5):
      for mask_sign,global_sign in product((-1,1),repeat=2):
       for q in range(8,17):
        ell,x,z,gap=3,1,2,1;Q=((1<<D)-1)*(q+z+gap)+1;B=(1<<(D-1))*Q
        modulus=2*B-1
        from math import gcd
        if gcd(q,modulus)!=1:continue
        coefficient=q*(B-1)**2;target=mask_sign-q*((B-1)*ell+1)
        quotient=(target*pow(coefficient,-1,modulus))%modulus or modulus
        J=(B-1)*quotient+ell;P=(B-1)*J+1;S=q*P;K=(S-mask_sign)//modulus;h=1+rng.randrange(4)
        assert K>h and S==(2*B-1)*K+mask_sign
        fixed={n:2 for n in compiler.NUMERALS}
        fixed.update(repunit_divisor=(1<<D)-1,recoder_radix=1<<(D-1),history_radix=8,terminal_scale=2,terminal_offset=1)
        values={n:1 for n in packet['parameters']+packet['auxiliaries']}
        values.update(x=x,z=z,program_E=1,program_duration_gap=2,input_slack=q-x-ell,power_gap=gap,duration_quotient=quotient,quotient_hat=h,fusion_output_slack=K-h)
        values.update({f'hist__Shat{i}':2+rng.randrange(3) for i in range(4)})
        rows=compiler.materialize(packet['source'],fixed);e=execute(rows,values)
        values[SLACK]=e['hist__P__10']-5-global_sign
        assert min(values.values())>0
        e=execute(rows,values)
        assert e[parent.UNIT]==mask_sign and e[UNITS['global_bound']]==global_sign
        L=e['fusion_low_q'];A=e['factored_pack_A_plus_one']-1;Bp=e['and__padded_B'];Zp=e['and__F3'];qj=e['and__q']
        fields=(qj-1-A-Bp+Zp,A-Zp,Bp-Zp,Zp)
        assert min(fields)>0 and sum(fields)==qj-1
        assert [f%16 for f in fields]==[1,4,2,8]
        assert sum(f*qj**i for i,f in enumerate(fields))==e['and__bs_packed']
        assert 0<e['factored_pack_low_A_plus_one']-1<L and 0<e['fusion_low_padded_B']<L and 0<e['fusion_low_F3']<L
        count+=1;negative_mask+=mask_sign<0;negative_global+=global_sign<0
    return dict(actual_source_outer_margin_cases=count,negative_mask=negative_mask,negative_global=negative_global,
        scope='Both signed outer bounds only, with positive actual-source fields; not native Pell zeros.')


def typed_history_audit():
    packet=build();rng=random.Random(260611);count=0
    for duration in range(1,5):
      for _ in range(8):
        tiles=[rng.randrange(4) for _ in range(duration)]
        states=[1]
        for tile in tiles:states.append((16*states[-1]+9) if tile in (1,2) else (2*states[-1]+1))
        fixed={n:2 for n in compiler.NUMERALS}
        fixed.update(repunit_divisor=7,recoder_radix=4,history_radix=32,terminal_scale=8,terminal_offset=4,upper_difference=14,upper_offset=9,upper_constant=34)
        values={n:1 for n in packet['parameters']+packet['auxiliaries']}
        values.update(program_E=1,program_duration_gap=2,x=1,z=2,input_slack=4,power_gap=1)
        values['hist__Ufinal']=states[-1]
        rows=compiler.materialize(packet['source'],fixed);e=execute(rows,values)
        floor=e['hist__height_sum__1'];D=1<<floor.bit_length();values['hist__height_slack']=D-floor;B=32*D
        P=B**duration;J=(P-1)//(B-1)
        Vstates=[rng.randrange(1,D) for _ in range(duration)]
        HU=sum(u*B**j for j,u in enumerate(states[:-1]));HV=sum(v*B**j for j,v in enumerate(Vstates))
        ZU=sum(states[j]*B**j for j,t in enumerate(tiles) if t in (1,2))
        ZV0=sum(Vstates[j]*B**j for j,t in enumerate(tiles) if t==0)
        ZV1=sum(Vstates[j]*B**j for j,t in enumerate(tiles) if t==1)
        values.update(hist__H_U=HU,hist__H_V=HV,hist__ZUhat0=ZU+1,hist__ZVhat0=ZV0+1,hist__ZVhat1=ZV1+1)
        values.update({f'hist__Shat{i}':1+sum(B**j for j,t in enumerate(tiles) if t==i) for i in range(4)})
        beta=P-HU-HV-ZU-ZV0-ZV1-3;assert beta>=((32-4)*D+3)*J-2>=17
        values[SLACK]=beta-1;e=execute(rows,values)
        assert e['hist__P__10']==P and e['hist__B__3']==B
        assert e[UNITS['upper']]==e[UNITS['global_bound']]==1
        assert e['hist__joined_H__89'] & e['hist__joined_M__95']==e['hist__joined_Z__96']
        count+=1
    return dict(actual_source_typed_history_cases=count,
        scope='Synthetic fixed affine coefficients, upper chronology and high-history AND only; not full universal/Pell zeros.')


def guards_audit():
    old=parent.build()
    mutations=[lambda p:p['comparisons'].pop(0),
      lambda p:p['source'].append(('bad_consumer','+',SLACK,1)),
      lambda p:p.update(public_registers={'extra':['hist__U_lhs__37']}),
      lambda p:p.update(auxiliaries=p['auxiliaries']+['bad']),
      lambda p:p.update(source=[(n,op,a,2) if n=='hist__U_lhs__37' else (n,op,a,b) for n,op,a,b in p['source']]),
      lambda p:p.update(unit_factors=p['unit_factors'][:-1]),
      lambda p:p.update(witnesses=p['witnesses']+1)]
    for mutate in mutations:
        bad=copy.deepcopy(old);mutate(bad)
        try:rewrite(bad)
        except (AssertionError,KeyError,ValueError):pass
        else:raise AssertionError('invalid parent accepted')
    return dict(rejected_incompatible_callers=len(mutations))


def verify():
    bases=[];selected=[];placements=[];frontiers={}
    for interface in (False,True):
      for n in parent.parent.parent.NORMALIZATIONS:
       for s in parent.parent.parent.SCALE_OPTIONS:
        b=parent.parent.parent.build_base(n,s,interface)
        old=parent.rewrite(parent.parent.rewrite(parent.parent.parent.factored.rewrite(b)))
        for mode in MODES:
            packet=rewrite(old,mode=mode)
            bases.append(dict(ledger(packet),audit=audit(packet,260000+len(bases))))
      seen=set()
      for witnesses in (None,43,44,45):
        frontier=[]
        for plan in parent.parent.parent.factored_frontier(witnesses):
            old_cost=plan['polynomial']['operations']-6
            old=parent.build(old_cost,merge_bound=interface,witnesses=witnesses)
            packet=rewrite(old);rec=ledger(packet)
            frontier.append((rec['polynomial']['operations'],rec['polynomial']['degree_upper_bound'],packet['witnesses']))
            key=(tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
            if key in seen:continue
            seen.add(key)
            for group in product(range(len(old['group_products'])),repeat=2):
                option=rewrite(old,groups=group)
                placements.append(dict(ledger(option),audit=audit(option,2601000+len(placements),4)))
            source,output=polynomial_source(packet);encoded=compiler.encode_source(source)
            selected.append(dict(rec,source=encoded,output=output,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
        if interface:frontiers[str(witnesses)]=frontier
    default=ledger(build());upper=ledger(build(mode='upper'))
    assert default['polynomial']['operations']==260 and upper['polynomial']['operations']==261
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_HISTORY_UNITS260',default=default,upper_intermediate=upper,
        mapped_frontiers=frontiers,bases=bases,placements=placements,selected_sources=selected,
        ledger_count=len(bases)+len(placements),complete_correction_cases=8*len(bases)+4*len(placements),
        signed_cases=4*len(bases)+2*len(placements),elementary=elementary_audit(),outer_margins=outer_margin_audit(),typed_history=typed_history_audit(),guards=guards_audit(),
        scope='Complete positive-zero bijection to guarded263 parent; beta_parent=beta_new+1 when the global unit is enabled. Upper-only preserves identical positive zeros. Actual U9/input/counter scope retained. Selected inherited partitions and placement search only; no enlarged-family partition optimum. No off-zero polynomial equality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default']);print(result['mapped_frontiers'])
