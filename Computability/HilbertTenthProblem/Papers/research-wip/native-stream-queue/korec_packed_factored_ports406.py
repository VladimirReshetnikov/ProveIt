"""Four exact additions saved in the complete U21 native packing graph.

Default one-program interface:406 operations. Two-program radix interface:405.
Every supplied coordinate and both complete polynomials are unchanged.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
import sympy as sp

import korec_packed_positive_program410 as positive
import korec_packed_program_radix409 as radix

core=positive.parent
execute=core.execute
polynomial_source=core.polynomial_source
degree_bound=core.degree_bound
ledger=core.ledger
FORMS=('fields','range_unit','units')
S='counter_factored_inner'
QMINUS='counter_factored_q_minus_one'
AONE='counter_factored_A_plus_one'
INDEX='native__bs_packed'


def leaves(v):
    if isinstance(v,str):return {v}
    if isinstance(v,dict):v=v.values()
    elif not isinstance(v,(list,tuple,set)):return set()
    return set().union(*(leaves(x) for x in v))


@lru_cache(None)
def build(form='units',*,program_radix=False):
    return rewrite((radix if program_radix else positive).build(form))


def rewrite(old):
    assert old.get('form') in FORMS and old.get('counter_computed_ports')
    base=radix if old.get('counter_program_radix') else positive
    assert old==base.build(old['form']),'requires a complete canonical410 or409 computed-fields U21 source'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    expected={
      'native__padded_A':('+','native__scaled_A',12),
      'native__F1':('-','native__padded_A','native__F3'),
      'native__F2':('-','native__padded_B','native__F3'),
      'native__free_00':('-','native__q','native__padded_A'),
      'native__free_00b':('-','native__free_00','native__F2'),
      'native__F0':('-','native__free_00b',1),
      'native__bs_p0':('*','native__q','native__F3'),
      'native__bs_p1':('+','native__F2','native__bs_p0'),
      'native__bs_p2':('*','native__q','native__bs_p1'),
      'native__bs_p3':('+','native__F1','native__bs_p2'),
      'native__bs_p4':('*','native__q','native__bs_p3'),
      INDEX:('+','native__F0','native__bs_p4')}
    assert all(rows.get(n)==row for n,row in expected.items())
    erased=set(expected)-{INDEX}
    for key in ('parameters','auxiliaries','comparisons','unit_factors','unit_register','interfaces','outer_pairs','public_registers'):
        assert not erased&leaves(old.get(key)),key
    assert all(n in expected or not erased&{a,b} for n,_,a,b in old['source'])
    added=[(QMINUS,'-','native__q',1),('counter_factored_q_plus_one','+','native__q',1),
        (AONE,'+','native__scaled_A',13),
        ('counter_factored_Z','*',QMINUS,'native__F3'),
        ('counter_factored_B','+','native__padded_B','counter_factored_Z'),
        ('counter_factored_scaled_B','*','counter_factored_q_plus_one','counter_factored_B'),
        (S,'+',AONE,'counter_factored_scaled_B'),(INDEX,'*',QMINUS,S)]
    assert not ({n for n,_,_,_ in added}-{INDEX})&set(rows)
    source=[row for row in old['source'] if row[0] not in expected]+added
    source=core.ps.sort_source(source,old['parameters']+old['auxiliaries'])
    packet=core.ps.metadata(dict(old,source=source,counter_factored_ports=True,
        factored_counter_parent=old,factored_erased_registers=sorted(erased),
        factored_index_identity='r=(q-1)*(A+1+(q+1)*(B+(q-1)*Z)); padded A+1 uses13 directly.',
        identical_complete_polynomial=True,identical_positive_coordinates=True))
    live=set(packet['parameters']+packet['auxiliaries'])|{n for n,_,_,_ in source}
    for key in ('canonical_native_registers','private_restoration_coordinates'):
        if key in packet:
            packet['historical_'+key]=packet[key]
            packet[key]=[n for n in packet[key] if n in live]
    core.ps.checked_source(source,packet['parameters'],packet['auxiliaries']);core.closure(packet)
    assert packet['operations']==old['operations']-4
    assert packet['multiplications']==old['multiplications']
    assert degree_bound(packet)==degree_bound(old)
    return packet


def restore_registers(env):
    q,A,B,Z=env['native__q'],env[AONE]-1,env['native__padded_B'],env['native__F3']
    f1=A-Z;f2=B-Z;f0=q-A-f2-1
    p0=q*Z;p1=f2+p0;p2=q*p1;p3=f1+p2;p4=q*p3
    assert f0+p4==env[INDEX]
    return dict(native__padded_A=A,native__F0=f0,native__F1=f1,native__F2=f2,
        native__free_00=q-A,native__free_00b=q-A-f2,
        native__bs_p0=p0,native__bs_p1=p1,native__bs_p2=p2,native__bs_p3=p3,native__bs_p4=p4)


def symbolic_audit():
    q,A,B,Z=sp.symbols('q A B Z')
    f1=A-Z;f2=B-Z;f0=q-A-B+Z-1
    old=f0+q*(f1+q*(f2+q*Z))
    new=(q-1)*(A+1+(q+1)*(B+(q-1)*Z))
    assert sp.Poly(old-new,q,A,B,Z).is_zero
    return str(sp.expand(new))


def audit(packet,seed,cases=32):
    rng=random.Random(seed);old=packet['factored_counter_parent'];counts=Counter()
    for j in range(cases):
        signed=j>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        new=execute(packet['source'],values);before=execute(old['source'],values)
        restored=restore_registers(new);assert set(restored)==set(packet['factored_erased_registers'])
        assert all(before[n]==v for n,v in restored.items())
        assert all(before[n]==new[n] for n,_,_,_ in old['source'] if n not in restored)
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos);os,oo=polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,values)[oo]
        counts['complete_graph_and_restoration_identities']+=1
        counts['complete_output_identities']+=2;counts['signed_assignments']+=signed
    return dict(counts)


def guards():
    rejected=0;old=positive.build()
    for packet in (dict(old,comparisons=[]),dict(old,interfaces={'hidden':['native__F0']}),
                   dict(old,source=old['source'][:-1]),positive.build('raw'),positive.build('coupled'),build()):
        try:rewrite(packet)
        except (AssertionError,KeyError):rejected+=1
        else:raise AssertionError('noncanonical source accepted')
    return rejected


def verify():
    records=[]
    for pr in (False,True):
      for form in FORMS:
        packet=build(form,program_radix=pr);ss,out=polynomial_source(packet)
        records.append(dict(program_radix=pr,form=form,ledger=ledger(packet),audit=audit(packet,406040+len(records)),
            source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest()))
    for pr,cost in ((False,406),(True,405)):
        assert ledger(build(program_radix=pr))['product']['operations']==cost
    return dict(status='PASS_KOREC_PACKED_FACTORED_PORTS406',records=records,
        symbolic_identity=symbolic_audit(),rejected_callers=guards(),
        scope='Exact complete polynomial identity on identical supplied integer coordinates, in both finalizers and both inherited program interfaces. Four additions saved; degree dictionaries unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for record in result['records']:print(record['program_radix'],record['form'],record['ledger']['product']['operations'])
