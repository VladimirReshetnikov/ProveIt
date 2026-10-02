"""Recover the U9 initial radix bound from its bounded-zero-run language.

A positive history height is supplied directly. The valid-program zero
bijection is stronger than the arbitrary-integer triangular output identity.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_terminal_bound255 as parent

compiler,execute=parent.compiler,parent.execute
polynomial_source,degree_bound=parent.polynomial_source,parent.degree_bound
HEIGHT,SLACK,INITIAL=parent.HEIGHT,parent.SLACK,parent.INITIAL


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):return set().union(*(leaves(v) for v in value.values()),set())
    if isinstance(value,(list,tuple)):return set().union(*(leaves(v) for v in value),set())
    return set()


def alias(value):
    if isinstance(value,str):return SLACK if value==HEIGHT else value
    if isinstance(value,dict):return {k:alias(v) for k,v in value.items()}
    if isinstance(value,list):return [alias(v) for v in value]
    if isinstance(value,tuple):return tuple(alias(v) for v in value)
    return value


def guard_parent(old):
    assert old.get('terminal_height_removed') and not old.get('initial_bound_recovered')
    expected=parent.rewrite(old['terminal_height_parent'])
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
    assert rows[HEIGHT]==('+',SLACK,INITIAL)
    assert rows['hist__B__3']==('*',HEIGHT,compiler.Numeral('history_radix'))
    assert rows['hist__range_cell__75']==('-',HEIGHT,1)
    assert {n for n,_,a,b in old['source'] if SLACK in (a,b)}=={HEIGHT}
    assert {n for n,_,a,b in old['source'] if HEIGHT in (a,b)}=={'hist__B__3','hist__range_cell__75'}
    assert SLACK in old['auxiliaries'] and HEIGHT not in old['auxiliaries']+old['parameters']
    for key in ('comparisons','unit_factors','interfaces','public_registers','fusion_interfaces','projected_coordinates'):
        assert HEIGHT not in leaves(old.get(key))


def rewrite(old):
    guard_parent(old)
    source=[(n,op,alias(a),alias(b)) for n,op,a,b in old['source'] if n!=HEIGHT]
    result=dict(old,source=source,operations=old['operations']-1,
        additions_subtractions=old['additions_subtractions']-1,
        initial_bound_parent=old,initial_bound_recovered=True,
        history_height_definition='D=hist__height_slack (positive height, no longer an additive gap)',
        history_height_register=SLACK,
        height_endpoint_hypothesis='Valid sentinel candidates have bounded zero runs; typed first digit recovers their initial radix bound, then transport bounds terminals',
        historical_initial_height_register=HEIGHT,
        identical_complete_polynomial=False,affine_complete_polynomial_identity=False,
        triangular_complete_polynomial_identity=True,
        identical_positive_zero_set=False,
        positive_zero_bijection='On inherited valid shifted program/input slices: D_new=W+eta_parent; eta_parent=D_new-W>=2 at new zeros',
        height_completeness_map='hist__height_slack_new=load__tag_input+hist__height_slack_parent',
        accepted_input_equivalence='Inherited valid shifted program/input slices; initial bound recovered from their bounded-zero-run language')
    compiler.check_source(result)
    return result


def build(operations=254,*,merge_bound=True,witnesses=None):
    return rewrite(parent.build(operations+1,merge_bound=merge_bound,witnesses=witnesses))


def initial_value(packet,values,numerals):
    """Execute only the literal loader cone; this is a map, not a free gate."""
    rows={n:(op,a,b) for n,op,a,b in packet['source']};needed=set();pending=[INITIAL]
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in rows and n not in needed:
            needed.add(n);pending.extend(rows[n][1:])
    source=[r for r in packet['source'] if r[0] in needed]
    assert SLACK not in leaves(source)
    return execute(compiler.materialize(source,numerals),values)[INITIAL]


def lift_to_parent(packet,values,numerals):
    result=dict(values);result[SLACK]-=initial_value(packet,values,numerals);return result


def project_from_parent(packet,values,numerals):
    result=dict(values);result[SLACK]+=initial_value(packet,values,numerals);return result


def ledger(packet):
    source,out=polynomial_source(packet);old=packet['initial_bound_parent'];before,_=polynomial_source(old)
    parent.parent.partitions.old.inherited.loader.source_closure(source,out)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==len(before)-1
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['comparisons']==old['comparisons']
    assert degree_bound(packet)['degree_upper_bound']<=degree_bound(old)['degree_upper_bound']
    return dict(parent_polynomial_operations=len(before),bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet.get('positive_scale_prefixes',()),
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
            degree_upper_bound=degree_bound(packet)['degree_upper_bound'],exact_degree_claimed=False),
        degree=degree_bound(packet))


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['initial_bound_parent'];bs,bo=polynomial_source(old);ns,no=polynomial_source(packet)
    counts=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS}
        if case==0:values[SLACK]=initial_value(packet,values,fixed)
        if case==1:values[SLACK]=1
        lifted=lift_to_parent(packet,values,fixed)
        assert project_from_parent(packet,lifted,fixed)==values
        a=execute(compiler.materialize(bs,fixed),lifted);b=execute(compiler.materialize(ns,fixed),values)
        assert a[HEIGHT]==b[SLACK]
        assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n!=HEIGHT)
        assert a[bo]==b[no]
        counts['complete_output_and_retained_register_identities']+=1
        counts['signed_assignments']+=signed
        if case<2:assert lifted[SLACK]<=0;counts['nonpositive_inverse_boundaries']+=1
        original={n:rng.randrange(1,6) for n in packet['parameters']+packet['auxiliaries']}
        positive_fixed={n:rng.randrange(1,6) for n in compiler.NUMERALS}
        projected=project_from_parent(packet,original,positive_fixed)
        assert min(projected.values())>0 and lift_to_parent(packet,projected,positive_fixed)==original
        c=execute(compiler.materialize(bs,positive_fixed),original);d=execute(compiler.materialize(ns,positive_fixed),projected)
        assert c[bo]==d[no] and all(c[n]==d[n] for n,_,_,_ in old['source'] if n!=HEIGHT)
        counts['complete_output_and_retained_register_identities']+=1
        counts['positive_parent_projections']+=1
    return dict(counts)


def word_bound_audit():
    counts=Counter()
    for beta in (2,3,4,7,13):
      for length in range(1,9):
       for prefix in range(1<<(length-1)):
        letters=['b' if prefix>>i&1 else 'c' for i in range(length-1)]+['b']
        code=''.join('1'+'0'*beta+'1' if c=='b' else '1' for c in letters[:-1])+'1'+'0'*beta
        V0=int('1'+code,2)
        for sign in (-1,1):
            I=V0 if sign==1 else V0-2
            bits=bin(I)[2:]
            assert I>0 and '0'*(beta+1) not in bits
            counts['bounded_zero_run_candidates']+=1
            for power in range(I.bit_length()+2):
             D=1<<power
             for gap in (beta+3,beta+5):
                b=(1<<gap)*D;r=I%b
                if r<D:
                    assert I<b and r==I
                    counts['initial_bound_recovered_cases']+=1
                if I>=b:
                    assert r>=D
                    counts['too_small_radix_exclusions']+=1
                counts['radix_residue_cases']+=1
    # A literal overlong zero run shows the language hypothesis is essential.
    for beta in (2,3,7,13):
        D=8;b=(1<<(beta+3))*D;I=b+1
        assert I>=b and I%b<D and '0'*(beta+1) in bin(I)[2:]
        counts['outside_language_counterexamples']+=1
    return dict(counts)


def pretyping_audit():
    counts=Counter()
    for D in (1,2,3,4,5,8):
     for ch in (32,64,256):
      b=ch*D
      for J in (1,2,3,7,17):
       for sign in (-1,1):
        P=(b-1)*J+sign
        assert P>=6 and b<=P+2 and 6*J<=P
        for selector in range(4):
         ss=[0]*4;ss[selector]=J
         for large in range(6):
            v=[1]*6;v[large]=P-5
            HU,HV,ZUh,ZV0h,ZV1h,slack=v
            C=sum(s*P**i for i,s in enumerate(ss));CM=J*sum(P**i for i in range(4))
            HB=HU+P*HV+P**2*HV;ZB=ZUh-1+P*(ZV0h-1)+P**2*(ZV1h-1)
            MB=(b-1)*(ss[1]+ss[2]+P*ss[0]+P**2*ss[1])
            HR=HU+P*HV;R=(D-1)*J;MR=R*(P+1)
            H=HB+P**3*C+P**7*HR+b*P**9
            M=MB+P**3*CM+P**7*MR+(b-1)*P**9
            Z=ZB+P**3*C+P**7*HR
            assert 0<=R<P and 0<=MR<P**2 and CM+2<P**4
            assert MB+P**3*CM<P**7 and H//P**9==b and M//P**9==b-1 and Z<P**9
            assert 0<=H<P**11 and 0<=M<P**11
            assert H-Z>0 and M-Z>1 and P**11-H-M+Z>=2
            assert ((ch-4)*D+3)*J-2>=17
            counts['pretyping_field_and_carry_cases']+=1
            counts['height_one_cases']+=D==1
            counts['negative_repunit_cases']+=sign==-1
    return dict(counts)


def guards_audit():
    old=parent.build();bad=[]
    for register in (HEIGHT,SLACK):
        p=copy.deepcopy(old);p['source'].append(('extra_'+register,'+',register,1));bad.append(p)
    for key in ('public_registers','fusion_interfaces'):
        p=copy.deepcopy(old);p[key]=dict(nested=[None,HEIGHT]);bad.append(p)
    for name in (HEIGHT,'hist__B__3','hist__range_cell__75'):
        p=copy.deepcopy(old);p['source']=[(n,'+' if op=='-' else '-',a,b) if n==name else (n,op,a,b) for n,op,a,b in p['source']];bad.append(p)
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=len(bad))


def mapped_frontier(records,witnesses=None):
    choices={}
    for r in records:
        if not r['bound_is_program_E'] or witnesses is not None and r['certificate']['witnesses']!=witnesses:continue
        key=r['polynomial']['operations'];score=(r['polynomial']['degree_upper_bound'],r['certificate']['witnesses'])
        if key not in choices or score<choices[key]:choices[key]=score
    answer=[];best=None
    for cost,(degree,w) in sorted(choices.items()):
        if best is None or degree<best:answer.append((cost,degree,w));best=degree
    return answer


def verify():
    records=[];selected=[];seen=set();engine=parent.parent.partitions
    for interface in (False,True):
      for n in engine.old.NORMALIZATIONS:
       for s in engine.old.SCALE_OPTIONS:
        packet=rewrite(parent.rewrite(parent.parent.rewrite(engine.base(n,s,interface))))
        records.append(dict(ledger(packet),audit=audit(packet,254000+len(records))))
      for w in (None,43,44,45):
       for plan in engine.frontier(w):
        old=parent.build(plan['polynomial']['operations']-2,merge_bound=interface,witnesses=w)
        key=(interface,tuple(old['normalized_prefixes']),tuple(old.get('positive_scale_prefixes',())),tuple(map(tuple,old['factor_partition'])),old['partition_anchor'])
        if key in seen:continue
        seen.add(key);packet=rewrite(old);rec=ledger(packet)
        records.append(dict(rec,audit=audit(packet,2541000+len(records))))
        source,out=polynomial_source(packet);encoded=compiler.encode_source(source)
        selected.append(dict(rec,source=encoded,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=254,multiplications=133,additions_subtractions=121,degree_upper_bound=1379,exact_degree_claimed=False)
    totals=Counter()
    for record in records:totals.update(record['audit'])
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_INITIAL_BOUND254',default=default,ledgers=records,selected_sources=selected,
        ledger_count=len(records),audit_totals=dict(totals),zero_run_bounds=word_bound_audit(),pretyping=pretyping_audit(),
        guards=guards_audit(),mapped_frontiers={str(w):mapped_frontier(records,w) for w in (None,43,44,45)},
        scope='Exact integer triangular output identity; full positive-zero bijection on valid shifted program/input slices after bounded-zero-run initial recovery. Mapped schedules only, no new exact partition search.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default']);print(result['mapped_frontiers'])
