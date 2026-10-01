"""Two exact paid selector-pair reuses below the complete U21 source380.

All supplied coordinates, comparisons, polynomials and degree bounds stay
unchanged. rewrite_rows is a local graph helper; it does not certify an
arbitrary caller's compiler semantics. rewrite requires canonical380.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_selector_sharing380 as parent

core=parent.core
execute,polynomial_source,degree_bound,ledger=parent.execute,parent.polynomial_source,parent.degree_bound,parent.ledger
FORMS=parent.FORMS
DELETED={'D5_110','linear_sum_165'}
REQUIRED={
    'D5_110':('+','edge_4','edge_16'),
    'D5_111':('+','D5_110','edge_18'),
    'coefficient_tail_198':('+','edge_18','edge_16'),
    'D4_109':('+','edge_14','edge_28'),
    'linear_sum_164':('+','linear_sum_163','edge_13'),
    'linear_sum_165':('+','linear_sum_164','edge_14'),
    'linear_sum_166':('+','linear_sum_165','edge_28')}
CHANGES={'D5_111':('+','edge_4','coefficient_tail_198'),
         'linear_sum_166':('+','D4_109','linear_sum_164')}
PUBLIC_KEYS=('parameters','auxiliaries','comparisons','outer_pairs','unit_factors',
    'unit_register','public_registers','interfaces','canonical_native_registers',
    'private_restoration_coordinates','ordinary_comparisons','group_products')


def rewrite_rows(old):
    """Return the guarded exact local rewrite; no metadata/domain mutation.

    A host wishing to inherit a complete compiler theorem must separately
    guard its canonical source, as rewrite() does. Declared exports of either
    erased private register are rejected, including nested containers.
    """
    core.ps.checked_source(old['source'],old['parameters'],old['auxiliaries'])
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert all(rows.get(n)==v for n,v in REQUIRED.items()),'literal shared-pair source required'
    for private,consumer in (('D5_110','D5_111'),('linear_sum_165','linear_sum_166')):
        assert {n for n,_,a,b in old['source'] if private in (a,b)}=={consumer},'private prefix has another consumer'
    for key in PUBLIC_KEYS:
        assert not DELETED&parent.leaves(old.get(key)),key
    # Every reused pair is a pure sum of edge leaves; no counter/control
    # dependency is imported into the current action before topological sort.
    assert rows['coefficient_tail_198']==('+','edge_18','edge_16')
    assert rows['D4_109']==('+','edge_14','edge_28')
    source=[(n,*CHANGES.get(n,(op,a,b))) for n,op,a,b in old['source'] if n not in DELETED]
    source=core.ps.sort_source(source,old['parameters']+old['auxiliaries'])
    core.ps.checked_source(source,old['parameters'],old['auxiliaries'])
    before=Counter(op for _,op,_,_ in old['source']);after=Counter(op for _,op,_,_ in source)
    assert len(source)==len(old['source'])-2 and before['+']==after['+']+2
    assert all(before[op]==after[op] for op in ('-','*'))
    return source


@lru_cache(None)
def build(form='units',*,program_radix=False):
    return rewrite(parent.build(form,program_radix=program_radix))


def rewrite(old):
    pr=old.get('counter_program_radix')
    assert type(pr) is bool and old.get('form') in FORMS
    assert old==parent.build(old['form'],program_radix=pr),'complete canonical selector380 source required'
    source=rewrite_rows(old)
    packet=core.ps.metadata(dict(old,source=source,counter_selector_pair_sharing=True,
        selector_pair_parent=old,selector_pair_changes=CHANGES,
        selector_pair_deleted=sorted(DELETED),
        selector_pair_scope='Exact integer graph identity on the same supplied coordinates, relative to selector380; no new semantic or native hypothesis.',
        identical_complete_polynomial=True,identical_positive_coordinates=True,
        identical_positive_zero_set=True,positive_zero_bijection=True))
    assert packet['operations']==old['operations']-2
    assert packet['multiplications']==old['multiplications']
    assert packet['additions_subtractions']==old['additions_subtractions']-2
    for key in PUBLIC_KEYS:
        assert packet.get(key)==old.get(key),key
    for sos in (False,True):
        assert degree_bound(packet,sum_of_squares=sos)==degree_bound(old,sum_of_squares=sos)
    core.closure(packet)
    return packet


def restore_registers(env):
    return {'D5_110':env['edge_4']+env['edge_16'],
            'linear_sum_165':env['linear_sum_164']+env['edge_14']}


def audit(packet,seed,cases=64):
    old=packet['selector_pair_parent'];rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        now=execute(packet['source'],values);before=execute(old['source'],values)
        restored=restore_registers(now)
        assert set(before)==set(now)|set(restored)
        assert all(now[n]==v for n,v in before.items() if n not in DELETED)
        assert all(restored[n]==before[n] for n in DELETED)
        assert now['D5_111']==sum(values[f'edge{i}_hat']-1 for i in (4,16,18))
        assert now['linear_sum_166']==now['linear_sum_164']+sum(values[f'edge{i}_hat']-1 for i in (14,28))
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos)
            os,oo=polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,values)[oo]
            counts['complete_output_identities']+=1;counts['signed_output_identities']+=signed
        counts['complete_retained_register_and_prefix_maps']+=1;counts['signed_assignments']+=signed
    return dict(counts)


def guards():
    old=parent.build();bad=[]
    bad.append(dict(old,source=old['source']+[('leak','+','D5_110',1)]))
    bad.append(dict(old,interfaces=dict(old['interfaces'],hidden=[{'prefix':'linear_sum_165'}])))
    bad.append(dict(old,public_registers={'hidden':(None,['D5_110'])}))
    bad.append(dict(old,ordinary_comparisons=[('linear_sum_165',1)]))
    bad.append(dict(old,source=[(n,'-',a,b) if n=='coefficient_tail_198' else (n,op,a,b) for n,op,a,b in old['source']]))
    for p in bad:
        try:rewrite_rows(p)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('malformed local source/export accepted')
    for p in (dict(old,comparisons=[]),build()):
        try:rewrite(p)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('noncanonical full source accepted')
    return len(bad)+2


def verify():
    records=[];totals=Counter()
    for pr in (False,True):
      for form in FORMS:
        packet=build(form,program_radix=pr);old=packet['selector_pair_parent']
        counts=audit(packet,378201+len(records));totals.update(counts)
        finalizers=[]
        for sos in (False,True):
            source,out=polynomial_source(packet,sum_of_squares=sos)
            previous,_=polynomial_source(old,sum_of_squares=sos)
            c=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            assert len(source)==len(previous)-2
            finalizers.append(dict(sum_of_squares=sos,operations=len(source),multiplications=c['M'],
                additions_subtractions=c['A'],output=out,degree=degree_bound(packet,sum_of_squares=sos)))
        source,out=polynomial_source(packet)
        records.append(dict(form=form,program_radix=pr,ledger=ledger(packet),audit=counts,
            literal_finalizer_ledgers=finalizers,source=source,output=out,
            parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest()))
    assert ledger(build())['product']['operations']==378
    assert ledger(build(program_radix=True))['product']['operations']==377
    return dict(status='PASS_KOREC_PACKED_SELECTOR_SHARING378',records=records,
        audit_totals=dict(totals),rejected_callers=guards(),local_row_changes=CHANGES,
        erased_private_registers=sorted(DELETED),
        scope='Exact complete integer polynomial identity relative to canonical selector380, with identical supplied domains and complete degree dictionaries; all six forms/interfaces and both finalizers. No new universality theorem or global arithmetic optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for record in result['records']:print(record['program_radix'],record['form'],record['ledger']['product'])
    print(result['audit_totals'])
