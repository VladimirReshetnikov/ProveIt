"""Seventeen additions saved by reusing paid U21 control subset sums.

The complete integer polynomial and every supplied coordinate are unchanged.
Default one-program source380; two-program radix source379.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_zero_range397 as parent

core=parent.core
execute,polynomial_source,degree_bound,ledger=parent.execute,parent.polynomial_source,parent.degree_bound,parent.ledger
FORMS=parent.FORMS
TOTAL='partition_66'
DELETED={f'partition_{i}' for i in range(34,66)}
TERMS=('edge_0','coefficient_tail_213','edge_2','coefficient_tail_203',
       'Z5_131','edge_8','edge_9','edge_11','coefficient_tail_184',
       'edge_13','edge_14','edge_21','edge_25','edge_27',
       'coefficient_group_176','edge_30','edge_32')
SUBSETS={'coefficient_tail_213':(1,4,10),
         'coefficient_tail_203':(3,6,7,15,16,18,26),
         'Z5_131':(5,17,19,23),
         'coefficient_tail_184':(12,20,22,24,31,33),
         'coefficient_group_176':(28,29)}


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):value=value.values()
    elif not isinstance(value,(list,tuple,set)):return set()
    return set().union(*(leaves(x) for x in value))


def selector_supports(old):
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    edges={f'edge_{i}':frozenset((i,)) for i in range(34)}
    @lru_cache(None)
    def support(n):
        if n in edges:return edges[n]
        op,a,b=rows[n]
        assert op=='+' and isinstance(a,str) and isinstance(b,str)
        left,right=support(a),support(b)
        assert not left&right,'a paid sum repeats a selector'
        return left|right
    found={n:tuple(sorted(support(n))) for n in TERMS}
    for name,expected in SUBSETS.items():assert found[name]==expected
    assert sorted(i for indices in found.values() for i in indices)==list(range(34))
    assert support(TOTAL)==frozenset(range(34))
    return found


@lru_cache(None)
def build(form='units',*,program_radix=False):
    return rewrite(parent.build(form,program_radix=program_radix))


def rewrite(old):
    pr=old.get('counter_program_radix')
    assert type(pr) is bool and old.get('form') in FORMS
    assert old==parent.build(old['form'],program_radix=pr),'requires the complete canonical zero_range397 caller'
    assert old['table']==core.TABLE and old['registers']==8 and len(old['edges'])==34
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows['partition_34']==('+','edge_0','edge_1')
    assert all(rows[f'partition_{i}']==('+',f'partition_{i-1}',f'edge_{i-33}') for i in range(35,67))
    assert all(n in DELETED|{TOTAL} or not DELETED&{a,b} for n,_,a,b in old['source'])
    for key in ('parameters','auxiliaries','comparisons','outer_pairs','unit_factors','unit_register',
                'public_registers','interfaces','canonical_native_registers','private_restoration_coordinates'):
        assert not DELETED&leaves(old.get(key)),key
    supports=selector_supports(old)
    added=[];value=TERMS[0]
    for i,term in enumerate(TERMS[1:]):
        name=TOTAL if i==len(TERMS)-2 else f'paid_selector_sum_{i}'
        assert name==TOTAL or name not in rows
        added.append((name,'+',value,term));value=name
    source=[row for row in old['source'] if row[0] not in DELETED|{TOTAL}]+added
    source=core.ps.sort_source(source,old['parameters']+old['auxiliaries'])
    packet=core.ps.metadata(dict(old,source=source,counter_selector_sharing=True,
        selector_sharing_parent=old,selector_shared_terms=list(TERMS),
        selector_shared_supports={n:list(v) for n,v in supports.items()},
        selector_sharing_erased=sorted(DELETED),
        selector_sharing_identity='J is the sum of five disjoint paid control subsets and twelve remaining edges.',
        identical_complete_polynomial=True,identical_positive_coordinates=True,
        identical_positive_zero_set=True,positive_zero_bijection=True,
        selector_sharing_scope='Exact integer graph identity on the same supplied coordinates; all parent compiler and chronology hypotheses retained.'))
    core.ps.checked_source(source,packet['parameters'],packet['auxiliaries']);core.closure(packet)
    assert packet['operations']==old['operations']-17
    assert packet['multiplications']==old['multiplications']
    assert packet['additions_subtractions']==old['additions_subtractions']-17
    assert degree_bound(packet)==degree_bound(old)
    for key in ('parameters','auxiliaries','comparisons','outer_pairs','unit_factors','unit_register','interfaces'):
        assert packet.get(key)==old.get(key),key
    return packet


def restore_registers(env):
    total=env['edge_0'];result={}
    for i in range(1,33):
        total+=env[f'edge_{i}'];result[f'partition_{i+33}']=total
    assert total+env['edge_33']==env[TOTAL]
    return result


def audit(packet,seed,cases=32):
    rng=random.Random(seed);old=packet['selector_sharing_parent'];counts=Counter()
    for j in range(cases):
        signed=j>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        new=execute(packet['source'],values);before=execute(old['source'],values)
        restored=restore_registers(new)
        assert set(restored)==DELETED and all(before[n]==v for n,v in restored.items())
        assert all(before[n]==new[n] for n,_,_,_ in old['source'] if n not in DELETED)
        assert new[TOTAL]==sum(values[f'edge{i}_hat']-1 for i in range(34))
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos);os,oo=polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,values)[oo]
            counts['complete_output_identities']+=1
            counts['signed_output_identities']+=signed
        counts['complete_register_restorations']+=1;counts['signed_assignments']+=signed
    return dict(counts)


def guards():
    old=parent.build();bad=[]
    bad.append(dict(old,source=old['source']+[('leak','+','partition_40',1)]))
    bad.append(dict(old,interfaces=dict(old['interfaces'],nested=[{'bad':'partition_40'}])))
    bad.append(dict(old,public_registers={'hidden':(None,['partition_65'])}))
    bad.append(dict(old,comparisons=[]))
    bad.append(dict(old,source=[(n,'-',a,b) if n=='coefficient_tail_203' else (n,op,a,b) for n,op,a,b in old['source']]))
    bad.append(build())
    for packet in bad:
        try:rewrite(packet)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('noncanonical source accepted')
    return len(bad)


def verify():
    records=[];totals=Counter()
    for pr in (False,True):
      for form in FORMS:
        packet=build(form,program_radix=pr);ss,out=polynomial_source(packet)
        old=packet['selector_sharing_parent'];checks=audit(packet,380170+len(records));totals.update(checks)
        prices=[]
        for sos in (False,True):
            source,output=polynomial_source(packet,sum_of_squares=sos)
            previous,_=polynomial_source(old,sum_of_squares=sos)
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            old_counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in previous)
            assert len(source)==len(previous)-17 and counts['M']==old_counts['M'] and counts['A']==old_counts['A']-17
            prices.append(dict(sum_of_squares=sos,operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],output=output))
        records.append(dict(program_radix=pr,form=form,ledger=ledger(packet),audit=checks,
            literal_finalizer_ledgers=prices,source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest()))
    for pr,cost in ((False,380),(True,379)):
        assert ledger(build(program_radix=pr))['product']['operations']==cost
    return dict(status='PASS_KOREC_PACKED_SELECTOR_SHARING380',records=records,
        audit_totals=dict(totals),selector_supports=selector_supports(parent.build()),
        rejected_callers=guards(),
        scope='Exact complete polynomial identity on identical supplied integer coordinates, both finalizers and inherited program interfaces. Seventeen additions saved; complete degree dictionaries and semantics unchanged. No global arithmetic optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for record in result['records']:print(record['program_radix'],record['form'],record['ledger']['product'])
    print(result['audit_totals'])
