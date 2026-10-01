"""Derive terminal radix bounds from transport instead of paying height:255.

The initial word remains in the height. Typed updates bound both terminal
digits afterwards. Positive completeness is an affine slack extension.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_height256 as parent

compiler,execute=parent.compiler,parent.execute
polynomial_source,degree_bound=parent.polynomial_source,parent.degree_bound
REMOVED=parent.SUM
HEIGHT,SLACK,UPPER,LOWER,INITIAL=parent.HEIGHT,parent.SLACK,parent.UPPER,parent.LOWER,parent.INITIAL


def guard_parent(old):
    assert old.get('dominated_height_endpoint_removed') and not old.get('terminal_height_removed')
    expected=parent.rewrite(old['height_parent'])
    for key in ('source','comparisons','parameters','auxiliaries','unit_factors',
                'group_products','factor_partition','partition_anchor','unit_register',
                'unit_product','fixed_numerals','width','interfaces','public_registers',
                'fusion_interfaces','projected_coordinates','normalized_prefixes',
                'positive_scale_prefixes','bound_is_program_E','operations',
                'multiplications','additions_subtractions','equations','witnesses',
                'initial_register','initial_value_expression','lower_unit_semantic_hypothesis',
                'history_height_definition','height_endpoint_hypothesis'):
        assert old.get(key)==expected.get(key),key
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[REMOVED]==('+',LOWER,INITIAL)
    assert rows[HEIGHT]==('+',SLACK,REMOVED)
    assert rows['hist__tag_terminal_scale']==('*',compiler.Numeral('terminal_scale'),UPPER)
    assert rows[LOWER]==('+','hist__tag_terminal_scale',compiler.Numeral('terminal_offset'))
    assert {n for n,_,a,b in old['source'] if REMOVED in (a,b)}=={HEIGHT}
    assert {n for n,_,a,b in old['source'] if SLACK in (a,b)}=={HEIGHT}
    for key in ('interfaces','public_registers','fusion_interfaces','projected_coordinates','comparisons','unit_factors'):
        assert REMOVED not in parent.leaves(old.get(key,{}))


def rewrite(old):
    guard_parent(old)
    source=[(n,'+',SLACK,INITIAL) if n==HEIGHT else (n,op,a,b)
            for n,op,a,b in old['source'] if n!=REMOVED]
    result=dict(old,source=source,operations=old['operations']-1,
        additions_subtractions=old['additions_subtractions']-1,
        terminal_height_parent=old,terminal_height_removed=True,
        history_height_definition='D=emitted_initial_minus_one+height_slack',
        height_endpoint_hypothesis='Initial digits lie below history radix; terminal radix bounds follow from typed updates and transport',
        historical_terminal_height_register=REMOVED,
        identical_complete_polynomial=False,affine_complete_polynomial_identity=True,
        identical_positive_zero_set=False,positive_zero_bijection=None,
        height_completeness_map='height_slack_new=height_slack_parent+tag_terminal',
        accepted_input_equivalence='Inherited valid shifted program/input slices; terminal bounds derived after native typing')
    compiler.check_source(result)
    return result


def build(operations=255,*,merge_bound=True,witnesses=None):
    return rewrite(parent.build(operations+1,merge_bound=merge_bound,witnesses=witnesses))


def terminal_value(values,numerals):
    return numerals['terminal_scale']*values[UPPER]+numerals['terminal_offset']


def lift_to_parent(packet,values,numerals):
    """Exact affine lift at the supplied fixed numerals; possibly nonpositive."""
    result=dict(values);result[SLACK]-=terminal_value(values,numerals);return result


def project_from_parent(packet,values,numerals):
    result=dict(values);result[SLACK]+=terminal_value(values,numerals);return result


def ledger(packet):
    source,out=polynomial_source(packet);old=packet['terminal_height_parent'];before,_=polynomial_source(old)
    parent.partitions.old.inherited.loader.source_closure(source,out)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==len(before)-1
    assert degree_bound(packet)==degree_bound(old)
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['comparisons']==old['comparisons']
    return dict(parent_polynomial_operations=len(before),bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
            degree_upper_bound=degree_bound(packet)['degree_upper_bound'],exact_degree_claimed=False),
        degree=degree_bound(packet))


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['terminal_height_parent'];bs,bo=polynomial_source(old);ns,no=polynomial_source(packet)
    for case in range(cases):
        draw=lambda:rng.randrange(1,6) if case<cases//2 else rng.randrange(-4,5)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS}
        if case==0:values[SLACK]=terminal_value(values,fixed)
        if case==1:values[SLACK]=1
        lifted=lift_to_parent(packet,values,fixed)
        assert project_from_parent(packet,lifted,fixed)==values
        a=execute(compiler.materialize(bs,fixed),lifted);b=execute(compiler.materialize(ns,fixed),values)
        assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n!=REMOVED)
        assert a[REMOVED]==b[INITIAL]+b[LOWER] and a[bo]==b[no]
        if case<2:assert lifted[SLACK]<=0
        original={n:rng.randrange(1,8) for n in packet['parameters']+packet['auxiliaries']}
        positive_numerals={n:rng.randrange(1,7) for n in compiler.NUMERALS}
        projected=project_from_parent(packet,original,positive_numerals)
        assert min(projected.values())>0 and lift_to_parent(packet,projected,positive_numerals)==original
        c=execute(compiler.materialize(bs,positive_numerals),original)
        d=execute(compiler.materialize(ns,positive_numerals),projected)
        assert c[bo]==d[no]
    return dict(complete_output_and_retained_register_identities=2*cases,
        signed_assignments=cases//2,positive_parent_projections=cases,nonpositive_parent_height_boundaries=2)


def transport_audit():
    """Exhaustive small canonical expansions, independent of all native APIs."""
    cases=equalities=nonzero=0
    for b in range(2,10):
      for duration in (1,2,3):
       P=b**duration
       # All N at small scales, extremal/interior samples at larger ones.
       words=range(P) if P<=81 else sorted({0,1,b-1,b,P//2,P-2,P-1})
       for N in words:
        for initial in range(b):
         combined=b*N+initial
         H,terminal=combined%P,combined//P
         assert 0<=terminal<b and b*N+initial==H+P*terminal
         nd=[N//b**j%b for j in range(duration)]
         hd=[H//b**j%b for j in range(duration)]
         assert hd[0]==initial and hd[1:]==nd[:-1] and terminal==nd[-1]
         for bad in (b,b+1,2*b):
          assert H+P*bad>b*N+initial
         cases+=1;equalities+=duration+1;nonzero+=terminal>0
    endpoints=0
    for W in (4,5,16,63,511):
      for eta in (1,2,7):
       D=W+eta
       for multiplier in (8,16,64):
        b=multiplier*D
        assert D>=4 and 0<=W-1<W+1<=D<b and D<b-1
        endpoints+=1
    return dict(canonical_transport_cases=cases,individual_digit_equalities=equalities,
        positive_terminal_cases=nonzero,pretyping_initial_bound_cases=endpoints,
        scope='Exact digit/domain fixtures, including initial0 and the eta1 boundary; no full native Pell zeros.')


def terminal_path_audit():
    """Actual four-tile paths whose final word exceeds their paid height."""
    records=[]
    for beta in (2,3,5,7,11,17):
        eb='1'+'0'*beta+'1'
        initial=int('1'+eb*(beta-1)+'1'+'0'*beta,2)
        upper=1;lower=initial;up=[];low=[];un=[];ln=[]
        for j in range(beta):
            up.append(upper);low.append(lower)
            upper=(1<<(beta+2))*upper+(1<<(beta+1))+1
            lower=8*lower+6 if j==0 else 2*lower
            un.append(upper);ln.append(lower)
        terminal=(1<<(beta+1))*upper+(1<<beta)
        assert terminal==lower
        D=1<<max(up+low).bit_length();b=(1<<(beta+3))*D;P=b**beta
        W=initial-1;eta=D-W
        pack=lambda digits:sum(v*b**j for j,v in enumerate(digits))
        HU,HV,NU,NV=map(pack,(up,low,un,ln))
        J=(P-1)//(b-1)
        selectors=[0,1,J-1,0]  # P_b followed by beta-1 D_b tiles.
        # Baseline2: upper exceptional class P_b/D_b, lower P_c and P_b.
        selected=[HU,0,initial]
        global_beta=P-HU-HV-sum(selected)-3
        assert min(eta,global_beta)>0 and max(up+low)<D<terminal<b
        assert sum(selectors)==J and all(v<b for v in un+ln)
        assert b*NU+1==HU+P*upper and b*NV+initial==HV+P*terminal
        assert eta-terminal<0
        records.append(dict(deletion_number=beta,duration=beta,initial_bits=initial.bit_length(),
            height_bits=D.bit_length(),terminal_bits=terminal.bit_length(),
            terminal_exceeds_height=True,affine_parent_gap_negative=True))
    return dict(actual_four_tile_paths=records,
        scope='One-step tag halts b^beta to b, packed as P_b D_b^(beta-1); valid outer histories and positive slacks, not full native Pell tuples or instantiated U9 program slices.')


def guards_audit():
    base=parent.build();bad=[]
    for coordinate in (REMOVED,SLACK):
        v=copy.deepcopy(base);v['source'].append(('extra_'+coordinate,'+',coordinate,1));bad.append(v)
    for key in ('public_registers','fusion_interfaces'):
        v=copy.deepcopy(base);v[key]=dict(nested=[None,REMOVED]);bad.append(v)
    for name in (HEIGHT,'hist__tag_terminal_scale',LOWER):
        v=copy.deepcopy(base);v['source']=[(n,'-',a,b) if n==name else (n,op,a,b) for n,op,a,b in v['source']];bad.append(v)
    for v in bad:
        try:rewrite(v)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=len(bad))


def verify():
    records=[];selected=[];seen=set();engine=parent.partitions
    for interface in (False,True):
      for n in engine.old.NORMALIZATIONS:
       for s in engine.old.SCALE_OPTIONS:
        packet=rewrite(parent.rewrite(engine.base(n,s,interface)))
        records.append(dict(ledger(packet),audit=audit(packet,255000+len(records))))
      for w in (None,43,44,45):
       for plan in engine.frontier(w):
        old=parent.build(plan['polynomial']['operations']-1,merge_bound=interface,witnesses=w)
        key=(interface,tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
        if key in seen:continue
        seen.add(key);packet=rewrite(old);rec=ledger(packet)
        records.append(dict(rec,audit=audit(packet,2551000+len(records))))
        source,out=polynomial_source(packet);encoded=compiler.encode_source(source)
        selected.append(dict(rec,source=encoded,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=255,multiplications=133,additions_subtractions=122,degree_upper_bound=1384,exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_TERMINAL_BOUND255',default=default,ledgers=records,selected_sources=selected,
        ledger_count=len(records),complete_output_and_retained_register_identities=16*len(records),
        signed_assignments=4*len(records),positive_parent_projections=8*len(records),
        nonpositive_parent_height_boundaries=2*len(records),transport_bounds=transport_audit(),
        terminal_exceeding_height_paths=terminal_path_audit(),guards=guards_audit(),
        mapped_frontiers={str(w):[(r['polynomial']['operations']-2,r['polynomial']['degree_upper_bound'],r['certificate']['witnesses'])
            for r in engine.frontier(w)] for w in (None,43,44,45)},
        scope='Accepted-input equivalence on inherited valid shifted program slices. Initial bound paid; terminal bounds derived after typing. Exact affine output identity and positive completeness, without a positive inverse claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default'])
