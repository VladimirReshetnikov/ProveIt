"""A sentinel obstruction absorbs the final U9 history comparison:259.

Positive-zero equivalence is asserted on the inherited valid program/input
slices. Arbitrary parameter tuples need not satisfy the sentinel hypothesis.
"""
import argparse
from collections import Counter
import copy
import hashlib
from itertools import product
import json
from pathlib import Path
import random

import neary_woods_universal_history_units260 as parent

compiler, execute = parent.compiler, parent.execute
def polynomial_source(packet):
    if packet['unit_product'] and packet['comparisons']==[(packet['unit_register'],1)]:
        assert packet['partition_anchor']==0 and len(packet['group_products'])==1
        output='lower_unit_output'
        assert output not in {r[0] for r in packet['source']}
        return packet['source']+[(output,'-',packet['unit_register'],1)],output
    return parent.polynomial_source(packet)


def degree_bound(packet):
    if packet['unit_product'] and packet['comparisons']==[(packet['unit_register'],1)]:
        # Degree-only zero residual: retain the frozen guarded main-norm
        # expansion, without adding an arithmetic gate or comparison.
        context=dict(packet,comparisons=[(0,0),*packet['comparisons']])
        result=parent.degree_bound(context)
        assert result['maximum_residual_degree_bound']==0
        return result
    return parent.degree_bound(packet)
PAIR = ('hist__V_lhs__39', 'hist__V_rhs__43')
DIFFERENCE, UNIT, PRODUCT = 'lower_history_difference', 'lower_history_unit', 'lower_history_product'


def guard_parent(old):
    assert old.get('history_unit_mode') == 'both'
    ancestor = old['history_unit_parent']
    parent.guard_parent(ancestor)
    expected = parent.rewrite(ancestor, mode='both', groups=old['history_unit_groups'])
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','fixed_numerals','width','interfaces','public_registers',
                'fusion_interfaces','projected_coordinates','normalized_prefixes',
                'positive_scale_prefixes','bound_is_program_E','operations',
                'multiplications','additions_subtractions','equations','witnesses'):
        assert old.get(key) == expected.get(key), key
    rows = {n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[PAIR[0]] == ('+','hist__V_update__38','load__tag_input')
    assert rows[PAIR[1]] == ('+','hist__H_V','hist__V_terminal__42')
    assert old['comparisons'].count(PAIR) == 1
    assert not {DIFFERENCE,UNIT,PRODUCT} & (set(rows)|set(old['parameters']+old['auxiliaries']))


def _rewrite(old, group):
    assert type(group) is int and 0 <= group < len(old['group_products'])
    previous = old['group_products'][group]
    source = old['source'] + [(DIFFERENCE,'-',PAIR[1],PAIR[0]),
        (UNIT,'+',DIFFERENCE,1),(PRODUCT,'*',previous,UNIT)]
    factors = old['unit_factors']+[UNIT]
    groups = [list(g) for g in old['factor_partition']]
    groups[group].append(len(factors)-1)
    products = list(old['group_products']); products[group] = PRODUCT
    comparisons = [(PRODUCT if a==previous else a,b) for a,b in old['comparisons'] if (a,b)!=PAIR]
    result = dict(old, source=source, unit_factors=factors, factor_partition=groups,
        group_products=products, comparisons=comparisons,
        unit_register=PRODUCT if old['unit_register']==previous else old['unit_register'],
        operations=old['operations']+3, multiplications=old['multiplications']+1,
        additions_subtractions=old['additions_subtractions']+2, equations=old['equations']-1,
        lower_unit_parent=old, lower_unit_group=group,
        identical_complete_polynomial=False, identical_positive_coordinates=True,
        identical_positive_zero_set=False,
        positive_zero_bijection='Identity on inherited valid program/input slices only',
        lower_unit_semantic_hypothesis='Loaded V0 is the sentinel of E(w), w ends in b, beta>=2.')
    compiler.check_source(result)
    return result


def rewrite(old, *, group=None):
    guard_parent(old)
    if group is not None:return _rewrite(old,group)
    choices=[_rewrite(old,j) for j in range(len(old['group_products']))]
    return min(choices,key=lambda p:(degree_bound(p)['degree_upper_bound'],p['lower_unit_group']))


def build(parent_operations=260, *, merge_bound=True, witnesses=None):
    return rewrite(parent.build(parent_operations,merge_bound=merge_bound,witnesses=witnesses))


def ledger(packet):
    old=packet['lower_unit_parent'];source,out=polynomial_source(packet)
    before,_=polynomial_source(old)
    parent.parent.parent.parent.loader.source_closure(source,out)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    saving=int(old['partition_anchor'] is not None and len(old['comparisons'])==2)
    assert len(source)==len(before)-saving
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['witnesses']==len(packet['auxiliaries'])
    degree=degree_bound(packet)
    return dict(parent_polynomial_operations=len(before),group=packet['lower_unit_group'],
        normalized_prefixes=packet['normalized_prefixes'],
        positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        bound_is_program_E=packet['bound_is_program_E'],factor_partition=packet['factor_partition'],
        partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
            degree_upper_bound=degree['degree_upper_bound'],exact_degree_claimed=False),
        lower_factor_degree=degree['factor_degree_bounds'][UNIT])


def audit(packet, seed, cases=8):
    rng=random.Random(seed);old=packet['lower_unit_parent']
    before,bo=polynomial_source(old);after,ao=polynomial_source(packet)
    anchor=old['partition_anchor'];chosen=packet['lower_unit_group']
    for case in range(cases):
        draw=lambda:rng.randrange(1,5) if case<cases//2 else rng.randrange(-3,4)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS}
        a=execute(compiler.materialize(before,fixed),values)
        b=execute(compiler.materialize(after,fixed),values)
        assert all(a[n]==b[n] for n,_,_,_ in old['source'])
        residual=a[PAIR[0]]-a[PAIR[1]];unit=1-residual
        assert b[UNIT]==unit
        G=[a[n] for n in old['group_products']];mods=[1]*len(G);mods[chosen]=unit
        for reg,indices,g,m in zip(packet['group_products'],packet['factor_partition'],G,mods):
            value=1
            for j in indices:value*=b[packet['unit_factors'][j]]
            assert b[reg]==value==g*m
        if anchor is None:
            correction=sum((g*m-1)**2-(g-1)**2 for g,m in zip(G,mods))
            expected=a[bo]-residual**2+correction
        else:
            correction=sum((G[j]*mods[j]-1)**2-(G[j]-1)**2 for j in range(len(G)) if j!=anchor)
            expected=mods[anchor]*(a[bo]+1)+mods[anchor]*G[anchor]*(correction-residual**2)-1
        assert b[ao]==expected
    return dict(complete_register_group_output_corrections=cases,signed_cases=cases//2)


def sentinel_audit():
    cases=append_cases=0
    for beta in range(2,13):
      for size in range(1,9):
       for prefix in product('bc',repeat=size-1):
        word=''.join(prefix)+'b'
        code=lambda v:''.join('1'+'0'*beta+'1' if c=='b' else '1' for c in v)
        P=int('1'+code(word[:-1]),2);V0=int('1'+code(word[:-1])+'1'+'0'*beta,2)
        assert P%2==1 and V0==P*2**(beta+1)+2**beta
        bad=bin(V0-2)[2:]
        assert bad==bin(P)[2:]+'0'+'1'*(beta-1)+'0'
        assert '101' in bad and V0-2>0
        for suffix in ('','0','110','1110','10101'):
            assert '101' in bad+suffix
            append_cases+=1
        cases+=1
    upper_cases=0
    for beta in range(2,13):
      for size in range(7):
       for word in product((0,1),repeat=size):
        upper='1'+''.join('1' if bit==0 else '1'+'0'*beta+'1' for bit in word)+'1'+'0'*beta
        assert '101' not in upper;upper_cases+=1
    # beta=1 is deliberately outside the theorem: the fixed obstruction fails.
    assert bin(3*4+2-2)[2:]=='1100'
    return dict(valid_tag_sentinels=cases,corrupted_sentinel_append_cases=append_cases,
        upper_tile_word_cases=upper_cases,beta_range=[2,12],
        scope='Exact finite word checks of the universal forbidden-subword proof; not Pell zeros.')


def guards_audit():
    base=parent.build();bad=[]
    for key in ('parameters','auxiliaries','comparisons','public_registers','fixed_numerals'):
        v=copy.deepcopy(base)
        if key=='comparisons':v[key]=v[key][1:]
        elif key=='fixed_numerals':v[key]={**v[key], 'new_role':1}
        elif key=='public_registers':v[key]=['hist__V_lhs__39']
        else:v[key]=v[key]+['unpaid']
        bad.append(v)
    v=copy.deepcopy(base);v['source'][0]=(v['source'][0][0],'-',*v['source'][0][2:]);bad.append(v)
    v=copy.deepcopy(base);v['history_unit_mode']='upper';bad.append(v)
    for v in bad:
        try:rewrite(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=len(bad))


def verify():
    records=[];selected=[];mapped={};seen=set()
    for interface in (False,True):
      for n in parent.parent.parent.parent.NORMALIZATIONS:
       for s in parent.parent.parent.parent.SCALE_OPTIONS:
        base=parent.parent.parent.parent.build_base(n,s,interface)
        old=parent.rewrite(parent.parent.rewrite(parent.parent.parent.rewrite(parent.parent.parent.parent.factored.rewrite(base))))
        p=rewrite(old);records.append(dict(ledger(p),audit=audit(p,259000+len(records))))
      for witnesses in (None,43,44,45):
        frontier=[]
        for plan in parent.parent.parent.parent.factored_frontier(witnesses):
            old=parent.build(plan['polynomial']['operations']-9,merge_bound=interface,witnesses=witnesses)
            p=rewrite(old);rec=ledger(p);frontier.append((rec['polynomial']['operations'],rec['polynomial']['degree_upper_bound'],p['witnesses']))
            key=(interface,tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
            if key in seen:continue
            seen.add(key)
            for group in range(len(old['group_products'])):
                q=rewrite(old,group=group);records.append(dict(ledger(q),audit=audit(q,2591000+len(records))))
            source,out=polynomial_source(p);encoded=compiler.encode_source(source)
            selected.append(dict(rec,source=encoded,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
        if interface:mapped[str(witnesses)]=frontier
    default=ledger(build())
    assert default['polynomial']==dict(operations=259,multiplications=133,additions_subtractions=126,degree_upper_bound=3861,exact_degree_claimed=False)
    assert default['certificate']==dict(operations=258,multiplications=133,additions_subtractions=125,equations=1,witnesses=43)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_LOWER_UNIT259',default=default,
        mapped_selected_schedules=mapped,ledgers=records,selected_sources=selected,
        ledger_count=len(records),complete_correction_cases=8*len(records),signed_cases=4*len(records),
        sentinel=sentinel_audit(),guards=guards_audit(),
        scope='Identical positive zeros on inherited valid program/input slices; no general invalid-parameter equivalence. Exact arbitrary-integer finalizer correction. Placement within selected partitions only, not enlarged-family optimality.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default']);print(result['mapped_selected_schedules'])
