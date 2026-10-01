"""Exact factored eight-digit repunit in the complete U21 selector378 source.

(1+D+...+D**7)=(1+D)*(1+D**2)*(1+D**4) saves two operations.
All supplied coordinates, public values, complete polynomials and degree
bounds are unchanged. rewrite_rows is only a guarded local graph helper.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_selector_sharing378 as parent

core=parent.core
execute,polynomial_source,degree_bound,ledger=parent.execute,parent.polynomial_source,parent.degree_bound,parent.ledger
FORMS=parent.FORMS
PUBLIC_KEYS=parent.PUBLIC_KEYS
DELETED={f'counter_repunit_{i}' for i in range(86,91)}
REQUIRED={
    'D2_73':('*','counter_radix_72','counter_radix_72'),
    'D3_74':('*','counter_radix_72','D2_73'),
    'D4_75':('*','D2_73','D2_73'),
    'D5_76':('*','D2_73','D3_74'),
    'D6_77':('*','D3_74','D3_74'),
    'D7_78':('*','D3_74','D4_75'),
    'counter_repunit_85':('+',1,'counter_radix_72'),
    **{f'counter_repunit_{i+84}':('+',f'counter_repunit_{i+83}',f'D{i}_{i+71}') for i in range(2,8)}}
ADDED=[('counter_repunit_D2_one','+','D2_73',1),
       ('counter_repunit_D4_one','+','D4_75',1),
       ('counter_repunit_first_product','*','counter_repunit_85','counter_repunit_D2_one')]
FINAL=('counter_repunit_91','*','counter_repunit_first_product','counter_repunit_D4_one')


def rewrite_rows(old):
    """Exact local identity; host completeness requires its own canonical guard."""
    core.ps.checked_source(old['source'],old['parameters'],old['auxiliaries'])
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert all(rows.get(n)==v for n,v in REQUIRED.items()),'literal powers and repunit chain required'
    assert not {r[0] for r in ADDED}&set(rows),'fresh factorization temporaries required'
    for i in range(86,91):
        private=f'counter_repunit_{i}'
        assert {n for n,_,a,b in old['source'] if private in (a,b)}=={f'counter_repunit_{i+1}'},'private repunit prefix has another consumer'
    for key in PUBLIC_KEYS:
        assert not DELETED&parent.parent.leaves(old.get(key)),key
    source=[FINAL if n=='counter_repunit_91' else (n,op,a,b)
            for n,op,a,b in old['source'] if n not in DELETED]+ADDED
    source=core.ps.sort_source(source,old['parameters']+old['auxiliaries'])
    core.ps.checked_source(source,old['parameters'],old['auxiliaries'])
    before=Counter(op for _,op,_,_ in old['source']);after=Counter(op for _,op,_,_ in source)
    assert len(source)==len(old['source'])-2
    assert after['*']==before['*']+2 and after['+']==before['+']-4 and after['-']==before['-']
    return source


@lru_cache(None)
def build(form='units',*,program_radix=False):
    return rewrite(parent.build(form,program_radix=program_radix))


def rewrite(old):
    pr=old.get('counter_program_radix')
    assert type(pr) is bool and old.get('form') in FORMS
    assert old==parent.build(old['form'],program_radix=pr),'complete canonical selector378 source required'
    source=rewrite_rows(old)
    packet=core.ps.metadata(dict(old,source=source,counter_repunit_factorization=True,
        repunit_factorization_parent=old,repunit_factorization_deleted=sorted(DELETED),
        repunit_factorization_added=[row[0] for row in ADDED],
        repunit_factorization_identity='sum(D**i for i in range(8))=(1+D)*(1+D**2)*(1+D**4)',
        repunit_factorization_scope='Exact integer graph identity on identical supplied coordinates relative to canonical selector378; no new native or compiler hypothesis.',
        identical_complete_polynomial=True,identical_positive_coordinates=True,
        identical_positive_zero_set=True,positive_zero_bijection=True))
    assert packet['operations']==old['operations']-2
    assert packet['multiplications']==old['multiplications']+2
    assert packet['additions_subtractions']==old['additions_subtractions']-4
    for key in PUBLIC_KEYS:assert packet.get(key)==old.get(key),key
    for sos in (False,True):
        assert degree_bound(packet,sum_of_squares=sos)==degree_bound(old,sum_of_squares=sos)
    core.closure(packet)
    return packet


def restore_registers(env):
    D=env['counter_radix_72']
    return {f'counter_repunit_{i+84}':sum(D**j for j in range(i+1)) for i in range(2,7)}


def audit(packet,seed,cases=64):
    old=packet['repunit_factorization_parent'];rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        now=execute(packet['source'],values);before=execute(old['source'],values)
        restored=restore_registers(now)
        added=set(packet['repunit_factorization_added'])
        assert set(before)-DELETED==set(now)-added
        assert all(now[n]==v for n,v in before.items() if n not in DELETED)
        assert all(restored[n]==before[n] for n in DELETED)
        D=now['counter_radix_72']
        assert now['counter_repunit_91']==sum(D**i for i in range(8))
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos)
            os,oo=polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,values)[oo]
            counts['complete_output_identities']+=1;counts['signed_output_identities']+=signed
        counts['complete_retained_register_and_prefix_maps']+=1;counts['signed_assignments']+=signed
    return dict(counts)


def guards():
    old=parent.build();bad=[]
    bad.append(dict(old,source=old['source']+[('leak','+','counter_repunit_87',1)]))
    bad.append(dict(old,interfaces=dict(old['interfaces'],hidden=[{'prefix':'counter_repunit_86'}])))
    bad.append(dict(old,public_registers={'hidden':(None,['counter_repunit_90'])}))
    bad.append(dict(old,ordinary_comparisons=[('counter_repunit_88',1)]))
    bad.append(dict(old,source=[(n,'+',a,b) if n=='D4_75' else (n,op,a,b) for n,op,a,b in old['source']]))
    bad.append(dict(old,source=[(n,'-',a,b) if n=='counter_repunit_89' else (n,op,a,b) for n,op,a,b in old['source']]))
    bad.append(dict(old,source=old['source']+[('counter_repunit_D2_one','+',1,1)]))
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
        packet=build(form,program_radix=pr);old=packet['repunit_factorization_parent']
        counts=audit(packet,376201+len(records));totals.update(counts)
        finalizers=[]
        for sos in (False,True):
            source,out=polynomial_source(packet,sum_of_squares=sos)
            previous,_=polynomial_source(old,sum_of_squares=sos)
            c=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            pc=Counter('M' if op=='*' else 'A' for _,op,_,_ in previous)
            assert len(source)==len(previous)-2 and c['M']==pc['M']+2 and c['A']==pc['A']-4
            finalizers.append(dict(sum_of_squares=sos,operations=len(source),multiplications=c['M'],
                additions_subtractions=c['A'],output=out,degree=degree_bound(packet,sum_of_squares=sos)))
        source,out=polynomial_source(packet)
        records.append(dict(form=form,program_radix=pr,ledger=ledger(packet),audit=counts,
            literal_finalizer_ledgers=finalizers,source=source,output=out,
            parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest()))
    assert ledger(build())['product']['operations']==376
    assert ledger(build(program_radix=True))['product']['operations']==375
    # Independent polynomial-coefficient expansion, with no values substituted.
    coefficients=[1]
    for shift in (1,2,4):
        result=[0]*(len(coefficients)+shift)
        for i,v in enumerate(coefficients):result[i]+=v;result[i+shift]+=v
        coefficients=result
    assert coefficients==[1]*8
    return dict(status='PASS_KOREC_PACKED_REPUNIT376',records=records,
        audit_totals=dict(totals),rejected_callers=guards(),symbolic_repunit_coefficients=coefficients,
        erased_private_registers=sorted(DELETED),added_source_rows=ADDED,replaced_final_row=FINAL,
        scope='Exact complete integer polynomial identity relative to canonical selector378, identical supplied domains and complete degree dictionaries; six forms/interfaces and both finalizers. Two fewer operations, with two more multiplications and four fewer additions. No global arithmetic optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for record in result['records']:print(record['program_radix'],record['form'],record['ledger']['product'])
    print(result['audit_totals'])
