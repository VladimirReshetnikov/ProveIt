"""A complete 440-operation universal equation through the literal C2 semigroup.

The positive ordinary input x is the only varying computational input.
One positive program parameter is compiled from a finite group presentation.
The paid loader excludes the power component's negative signed-unit branch.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import prod
from pathlib import Path
import random

import tseytin_c2_word_history as word
import pell_fixed_affine_exponent as power
import tseytin_affine_power_query_loader as loader

execute = word.execute


def exponent_name(value):
    return 'exp__'+value if isinstance(value, str) and value != 'x' else value


def build(*, merge_units=True):
    assert type(merge_units) is bool
    w, p, q = word.build(), power.build(), loader.build()
    source = list(w['source'])
    source += [(exponent_name(n), op, exponent_name(a), exponent_name(b))
               for n, op, a, b in p['source']]
    alias = lambda v: exponent_name('Q') if v == 'Q' else v
    source += [(n, op, alias(a), alias(b)) for n, op, a, b in q['source']]
    ordinary = list(w['comparisons'][:-1])+list(q['comparisons'])
    power_unit = exponent_name(p['unit_register'])
    unit = w['unit_register']
    comparisons = list(ordinary)
    if merge_units:
        source.append(('c2_power_unit', '*', unit, power_unit))
        unit = 'c2_power_unit'
    else:
        comparisons.append((power_unit, 1))
    comparisons.append((unit, 1))
    parameters = ['x', 'program_A']
    auxiliaries = ['word']+list(w['auxiliaries'])+list(map(exponent_name, p['auxiliaries']))
    source = word.scale.sort_source(source, parameters+auxiliaries)
    word.scale.checked_source(source, parameters, auxiliaries)
    return word.scale.metadata(dict(source=source, comparisons=comparisons,
        ordinary_comparisons=ordinary, parameters=parameters, auxiliaries=auxiliaries,
        unit_register=unit, word_unit_register=w['unit_register'],
        power_unit_register=power_unit, merge_units=merge_units,
        word_factors=list(w['unit_factors']), power_factors=list(map(exponent_name, p['unit_factors'])),
        interfaces=dict(input='x', program='program_A', encoded_word='word', power=exponent_name('Q')),
        positive_integer_domain=True,
        program_recipe=q['valid_program_recipe'],
        semantics='For every CE positive set, the effective presentation recipe supplies one positive program_A whose positive zeros project exactly to that set.'))


def checked_packet(packet):
    assert packet == build(merge_units=packet['merge_units']), 'literal canonical composition required'


def polynomial_source(packet=None, *, sum_of_squares=False):
    if packet is None: packet = build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet, sum_of_squares=sum_of_squares)


def degree_bound(packet=None, *, sum_of_squares=False):
    if packet is None: packet = build()
    checked_packet(packet)
    wd = word.norms.degree_bound(word.build())
    pd = power.degrees()[0]
    pf = [pd[n] for n in power.FACTOR_NAMES]
    power_degree = sum(pf)
    assert power_degree == 54
    # Both literal parent graphs are unchanged. Q=x+delta has degree one;
    # word remains a supplied coordinate, so the query comparison has degree7.
    residual = max(wd['maximum_residual_degree_bound'], loader.build()['degree_upper_bound'])
    unit = wd['unit_degree_bound']
    if packet['merge_units']: unit += power_degree
    else: residual = max(residual, power_degree)
    return dict(degree_upper_bound=2*max(unit,residual) if sum_of_squares else unit+2*residual,
        unit_degree_bound=unit, maximum_residual_degree_bound=residual,
        word_factor_degree_bounds=wd['factor_degree_bounds'], power_factor_degrees=pf,
        exact_degree_claimed=False)


def ledger(packet=None, *, sum_of_squares=False):
    if packet is None: packet = build()
    source, output = polynomial_source(packet, sum_of_squares=sum_of_squares)
    count = Counter(op for _, op, _, _ in source)
    return dict(certificate={k:packet[k] for k in
        ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source), multiplications=count['*'],
            additions_subtractions=count['+']+count['-'], output=output,
            **degree_bound(packet, sum_of_squares=sum_of_squares)))


def sign_filter():
    """Exact fixed residue certificates, not a sampled sign exclusion."""
    B, d = loader.B, loader.DENOMINATOR
    h = loader.COEFFICIENTS
    assert B == 2**96 and d == B*B-1 and B % 7 == 1
    closed = [( -65*B*B+229376*B+229441)//7,
              -8**5*(B*B+B-4096), 0,
              -8**9*(B*B-512*B-512),
              -8**12*(B*B+B-512), 0,
              8**15*(65*B*B-72)//7]
    assert closed == h
    records = []
    for parity, a, b, quotient in (
        (0, 15759360, 558888960, 308535569154048),
        (1, 24115200, 550533120, 590560301678592-584115552256*B)):
        residue = a*B+b
        cleared = h[6]+16**2*h[4]+16**3*B**parity*h[3]+16**5*B**parity*h[1]+16**6*h[0]
        assert cleared == quotient*d+16**6*residue
        Qmod = B**parity*pow(16,-1,d) % d
        direct = sum(h[i]*pow(Qmod,i,d) for i in (0,1,3,4,6)) % d
        assert direct == residue and 0 < residue < d
        records.append(dict(parity=parity, Q_residue=Qmod, numerator_residue=residue,
            positive_residue_coefficients=[a,b], exact_cleared_quotient=quotient))
    # There are just two residue classes, because B²=1 modulo d.
    assert pow(B,2,d) == 1 and (16*pow(16,-1,d)) % d == 1
    return dict(B=B, denominator=d, tail_coefficients=h, cases=records,
        conclusion='For A congruent h6 mod d, Q=B**x/16 makes the paid numerator nonzero mod d for either parity of positive x.')


def closure(source, output, inputs):
    word.scale.checked_source(source, inputs, [])
    rows = {n:(a,b) for n,_,a,b in source}
    live=set(); pending=[output]
    while pending:
        n=pending.pop()
        if not isinstance(n,str) or n not in rows or n in live: continue
        live.add(n); pending.extend(rows[n])
    assert live == set(rows), 'dead paid gate'
    return len(live)


def assignment_audit(cases=128):
    rng=random.Random(440652)
    w,p,q=word.build(),power.build(),loader.build()
    packets=[(build(merge_units=m),sos) for m in (False,True) for sos in (False,True)]
    schedules=[polynomial_source(v,sum_of_squares=sos) for v,sos in packets]
    totals=Counter()
    for case in range(cases):
        signed=case>=cases//2
        draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
        values={n:draw() for n in packets[0][0]['parameters']+packets[0][0]['auxiliaries']}
        wv={n:values[n] for n in w['parameters']+w['auxiliaries']}
        pv={n:values[exponent_name(n)] for n in p['parameters']+p['auxiliaries']}
        we=word.execute(w['source'],wv)
        pe=power.execute(p['source'],pv)
        pf=power.factors(pv)
        assert all(pe[n]==pf[n] for n in p['unit_factors'])
        W=prod(we[n] for n in w['unit_factors']); P=prod(pf.values())
        at=lambda v:we[v] if isinstance(v,str) else v
        residuals=[at(a)-at(b) for a,b in w['comparisons'][:-1]]
        Q=pv['x']+pv['delta']; A=values['program_A']
        query=A*Q**6+sum(loader.COEFFICIENTS[i]*Q**i for i in (0,1,3,4))-loader.DENOMINATOR*values['word']
        residuals.append(query)
        S=sum(v*v for v in residuals)
        for (packet,sos),(source,out) in zip(packets,schedules):
            env=execute(source,values)
            assert all(env[n]==we[n] for n,_,_,_ in w['source'])
            assert all(env[exponent_name(n)]==pe[n] for n,_,_,_ in p['source'])
            actual=[env[a]-env[b] if isinstance(b,str) else env[a]-b for a,b in packet['ordinary_comparisons']]
            assert actual==residuals
            if packet['merge_units']:
                expected=(W*P-1)**2+S if sos else W*P*(1+S)-1
            else:
                expected=(W-1)**2+(P-1)**2+S if sos else W*(1+(P-1)**2+S)-1
            assert env[out]==expected
            totals['complete_parent_register_and_manual_output_identities']+=1
            totals['signed_output_identities']+=signed
    return dict(totals)


def query_audit():
    cases=0
    for rank in (2,4,6):
      for relators in ((),((1,2,-1,-2),)):
        S=loader.program_word(rank,relators); A=loader.program_parameter(S)
        assert A % loader.DENOMINATOR == loader.COEFFICIENTS[6] % loader.DENOMINATOR
        for x in range(1,17):
            p=build(); values={n:1 for n in p['parameters']+p['auxiliaries']}
            values.update(x=x,program_A=A,word=loader.encode(loader.query_word(S,x)))
            values['exp__delta']=loader.B**x-x
            assert min(values.values())>0
            e=execute(p['source'],values)
            assert e['exp__Q']==loader.B**x
            assert e['query_numerator']==e['query_scaled_word']
            assert word.decode(values['word'])==loader.query_word(S,x)
            badQ=loader.B**x//16
            numerator=A*badQ**6+sum(loader.COEFFICIENTS[i]*badQ**i for i in (0,1,3,4))
            expected=sign_filter()['cases'][x%2]['numerator_residue']
            assert numerator % loader.DENOMINATOR == expected
            cases+=1
    return dict(literal_query_and_negative_branch_examples=cases,
        scope='Complete source assignments check the paid query interface only; placeholder native and exponent auxiliaries are not claimed to be zeros.')


def guards():
    p=build()
    bad=[dict(p,source=p['source'][:-1]), dict(p,auxiliaries=p['auxiliaries'][:-1]),
         dict(p,comparisons=p['comparisons'][:-1]), dict(p,unit_register=p['word_unit_register']),
         dict(p,interfaces={'power':'word'})]
    for v in bad:
        for operation in (polynomial_source,degree_bound):
            try:operation(v)
            except AssertionError:pass
            else:raise AssertionError('mutated composition accepted')
    return 2*len(bad)


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge); source,out=polynomial_source(p,sum_of_squares=sos)
        rec=ledger(p,sum_of_squares=sos)
        assert rec['polynomial']['operations']==(440 if merge else 442)
        assert p['witnesses']==65 and p['equations']==(7 if merge else 8)
        assert p['operations']==(420 if merge else 419)
        assert closure(source,out,p['parameters']+p['auxiliaries'])==len(source)
        rec.update(merge_units=merge,sum_of_squares=sos,source=source,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    assert records[2]['polynomial']['multiplications']==200
    assert records[2]['polynomial']['additions_subtractions']==240
    assert records[2]['polynomial']['degree_upper_bound']==5868
    assert records[0]['polynomial']['degree_upper_bound']==5814
    return dict(status='PASS_TSEYTIN_UNIVERSAL440',forms=records,sign_filter=sign_filter(),
        source_audit=assignment_audit(),query_audit=query_audit(),rejected_mutations=guards(),
        scope='Complete source and theorem via effective group embedding and actual C2 history. No general Higman compilation or full giant native/exponent zero is numerically materialized. Overall75/87 record unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit'])
    print([(r['merge_units'],r['sum_of_squares'],r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in result['forms']])
