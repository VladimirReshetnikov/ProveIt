"""Seven exact gates saved by sharing the paid eight-term repunit.

R24(P)=R8(P)*(1+P**8+P**16). The canonical425 graph already pays
R8, P**8 and P**16. Replacing ten private-chain rows with three
rows preserves the complete integer polynomial and every supplied domain.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_universal425 as parent

word=parent.word
scale=word.scale
execute=word.execute
FINAL='repunit_product__215'
DELETED={'repunit_tail__206','P3__207','repunit_factor__208',
         'repunit_product__209','P6__210','repunit_factor__211',
         'repunit_product__212','P12__213','repunit_factor__214'}
ADDED=[('c2_repunit_outer_pair','+','P8__277','P16__279'),
       ('c2_repunit_outer_factor','+','c2_repunit_outer_pair',1)]
REPLACEMENT=(FINAL,'*','repunit_product__253','c2_repunit_outer_factor')
REQUIRED={
    'repunit_factor__204':('+','P__30',1),
    'P2__205':('*','P__30','P__30'),
    'repunit_tail__206':('+','P2__205','repunit_factor__204'),
    'P3__207':('*','P2__205','P__30'),
    'repunit_factor__208':('+','P3__207',1),
    'repunit_product__209':('*','repunit_factor__208','repunit_tail__206'),
    'P6__210':('*','P3__207','P3__207'),
    'repunit_factor__211':('+','P6__210',1),
    'repunit_product__212':('*','repunit_factor__211','repunit_product__209'),
    'P12__213':('*','P6__210','P6__210'),
    'repunit_factor__214':('+','P12__213',1),
    FINAL:('*','repunit_factor__214','repunit_product__212'),
    'repunit_factor__249':('+','P2__205',1),
    'repunit_product__250':('*','repunit_factor__204','repunit_factor__249'),
    'P4__251':('*','P2__205','P2__205'),
    'repunit_factor__252':('+','P4__251',1),
    'repunit_product__253':('*','repunit_factor__252','repunit_product__250'),
    'P8__277':('*','P4__251','P4__251'),
    'P16__279':('*','P8__277','P8__277')}
CONSUMERS={n:{t for t,(_,a,b) in REQUIRED.items() if n in (a,b)} for n in DELETED}


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):value=list(value.keys())+list(value.values())
    elif not isinstance(value,(list,tuple,set)):return set()
    return set().union(*(leaves(v) for v in value))


def rewrite_rows(old):
    """Guarded local identity only; a complete host needs its own theorem."""
    scale.checked_source(old['source'],old['parameters'],old['auxiliaries'])
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert all(rows.get(n)==row for n,row in REQUIRED.items()),'literal repunits and paid powers required'
    for n in DELETED:
        assert {t for t,_,a,b in old['source'] if n in (a,b)}==CONSUMERS[n],'private repunit value has an extra consumer'
    # Inspect every active field, including nested caller exports and keys.
    assert not DELETED&leaves({k:v for k,v in old.items() if k!='source'}),'private repunit value is exported'
    fresh={n for n,_,_,_ in ADDED}
    assert not fresh&(set(rows)|set(old['parameters']+old['auxiliaries'])),'fresh temporaries required'
    source=[REPLACEMENT if n==FINAL else (n,op,a,b)
            for n,op,a,b in old['source'] if n not in DELETED]+ADDED
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    before=Counter(op for _,op,_,_ in old['source']);after=Counter(op for _,op,_,_ in source)
    assert len(source)==len(old['source'])-7
    assert after['*']==before['*']-5 and after['+']==before['+']-2 and after['-']==before['-']
    return source


def naive_degrees(source,inputs):
    return parent.sharing.naive_degrees(source,inputs)


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge) is bool and old==parent.build(merge_units=merge),'entire canonical425 parent required'
    source=rewrite_rows(old)
    result=scale.metadata(dict(old,source=source,repunit_sharing=True,
        repunit_sharing_parent=old,repunit_sharing_deleted=sorted(DELETED),
        identical_complete_polynomial=True,identical_positive_coordinates=True,
        identical_positive_zero_set=True,positive_zero_bijection=True,
        repunit_sharing_identity='sum(P**i for i in range(24))=sum(P**i for i in range(8))*(1+P**8+P**16)',
        repunit_sharing_scope='Exact all-integer source substitution relative to the canonical425 merged/separate packet. No endpoint, loader, native, or program hypothesis changes.'))
    old_degrees=naive_degrees(old['source'],old['parameters']+old['auxiliaries'])
    new_degrees=naive_degrees(source,old['parameters']+old['auxiliaries'])
    assert all(new_degrees[n]==d for n,d in old_degrees.items() if n not in DELETED)
    for k in ('parameters','auxiliaries','comparisons','ordinary_comparisons','unit_register',
              'word_unit_register','power_unit_register','word_factors','power_factors','interfaces',
              'program_recipe','projection','positive_integer_domain'):
        assert result[k]==old[k],k
    return result


@lru_cache(None)
def build(*,merge_units=True):
    return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'canonical repunit-sharing packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    # Every retained propagated degree agrees, and both exact main-norm
    # cancellation graphs are unchanged. Preserve the entire dictionary.
    return parent.degree_bound(packet['repunit_sharing_parent'],sum_of_squares=sum_of_squares)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    count=Counter(op for _,op,_,_ in rows)
    return dict(certificate={k:packet[k] for k in
        ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=count['*'],
            additions_subtractions=count['+']+count['-'],output=out,
            **degree_bound(packet,sum_of_squares=sum_of_squares)))


def restore_registers(env):
    P=env['P__30']
    return {'repunit_tail__206':1+P+P**2,'P3__207':P**3,
        'repunit_factor__208':1+P**3,'repunit_product__209':sum(P**i for i in range(6)),
        'P6__210':P**6,'repunit_factor__211':1+P**6,
        'repunit_product__212':sum(P**i for i in range(12)),
        'P12__213':P**12,'repunit_factor__214':1+P**12}


def assignment_audit(packet,seed,cases=96):
    old=packet['repunit_sharing_parent'];rng=random.Random(seed);counts=Counter()
    schedules=[(polynomial_source(packet,sum_of_squares=s),parent.polynomial_source(old,sum_of_squares=s))
               for s in (False,True)]
    for case in range(cases):
        signed=case>=cases//2
        draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        if case in (0,cases//2):
            values.update({f'Shat{i}':1 for i in range(24)})
            counts['zero_unhatted_selector_cases']+=1
        now=execute(packet['source'],values);previous=execute(old['source'],values)
        assert set(previous)-DELETED==set(now)-{n for n,_,_,_ in ADDED}
        assert all(now[n]==v for n,v in previous.items() if n not in DELETED)
        restored=restore_registers(now)
        assert set(restored)==DELETED and all(restored[n]==previous[n] for n in DELETED)
        P=now['P__30'];assert now[FINAL]==sum(P**i for i in range(24))
        for (ns,no),(os,oo) in schedules:
            assert execute(ns,values)[no]==execute(os,values)[oo]
            counts['complete_output_identities']+=1
            counts['signed_output_identities']+=signed
        counts['complete_retained_register_and_restoration_maps']+=1
        counts['signed_assignments']+=signed
    return dict(counts)


def guards():
    old=parent.build();bad=[]
    for n in sorted(DELETED):
        bad.append(dict(old,source=old['source']+[('extra_consumer','+',n,1)]))
    for n in ('repunit_product__253','P8__277','P16__279',FINAL):
        bad.append(dict(old,source=[(t,'+',a,b) if t==n else (t,op,a,b) for t,op,a,b in old['source']]))
    bad.extend((dict(old,interfaces={'nested':[{'private':'P3__207'}]}),
                dict(old,public_registers={'P6__210':None}),
                dict(old,source=old['source']+[('c2_repunit_outer_pair','+',1,1)])))
    for candidate in bad:
        try:rewrite_rows(candidate)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('invalid local host accepted')
    canonical=[dict(old,comparisons=[]),dict(old,parameters=['x']),
               dict(old,program_recipe='arbitrary positive parameter')]
    for candidate in canonical:
        try:rewrite(candidate)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('invalid canonical parent accepted')
    for candidate in (dict(build(),interfaces={}),dict(build(),source=build()['source'][:-1])):
        for operation in (polynomial_source,degree_bound):
            try:operation(candidate)
            except (AssertionError,KeyError,TypeError):pass
            else:raise AssertionError('altered successor accepted')
    return len(bad)+len(canonical)+4


def verify():
    records=[];totals=Counter()
    for merge in (False,True):
        packet=build(merge_units=merge);old=packet['repunit_sharing_parent']
        totals.update(assignment_audit(packet,418652+int(merge)))
        for sos in (False,True):
            rows,out=polynomial_source(packet,sum_of_squares=sos)
            previous,_=parent.polynomial_source(old,sum_of_squares=sos)
            rec=ledger(packet,sum_of_squares=sos)
            assert len(rows)==(418 if merge else 420)
            assert packet['operations']==(398 if merge else 397)
            assert packet['witnesses']==65 and packet['equations']==(7 if merge else 8)
            assert degree_bound(packet,sum_of_squares=sos)==parent.degree_bound(old,sum_of_squares=sos)
            c=Counter(op for _,op,_,_ in rows);pc=Counter(op for _,op,_,_ in previous)
            assert c['*']==pc['*']-5 and c['+']==pc['+']-2 and c['-']==pc['-']
            parent.baseline.closure(rows,out,packet['parameters']+packet['auxiliaries'])
            rec.update(merge_units=merge,sum_of_squares=sos,source=rows,output=out,
                parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],comparisons=packet['comparisons'],
                source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            records.append(rec)
    coefficients=[0]*24
    for i in range(8):
        for j in (0,8,16):coefficients[i+j]+=1
    assert coefficients==[1]*24
    assert records[2]['polynomial']['multiplications']==194
    assert records[2]['polynomial']['additions_subtractions']==224
    assert [r['polynomial']['degree_upper_bound'] for r in records]==[5814,11352,5868,11460]
    return dict(status='PASS_TSEYTIN_REPUNIT_SHARING418',forms=records,audit_totals=dict(totals),
        repunit_coefficients=coefficients,erased_private_registers=sorted(DELETED),
        added_rows=ADDED,replaced_row=REPLACEMENT,rejected_callers=guards(),
        scope='Exact integer polynomial and supplied-coordinate identity with canonical425 merged/separate sources, both finalizers. Uniform seven-gate saving (5M+2A), unchanged complete degree dictionaries. No global arithmetic optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['audit_totals'])
    print([(r['merge_units'],r['sum_of_squares'],r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in result['forms']])
