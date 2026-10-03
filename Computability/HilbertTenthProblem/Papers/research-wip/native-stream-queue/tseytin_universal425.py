"""Complete Tseytin universality with a paid fused initial endpoint:425 gates.

Use the362-operation shared word source and52-operation exact exponent.
Load the chronological initial endpoint directly, saving its two gates.
The exponent sign filter survives the factor-eight change of query code.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import prod
from pathlib import Path
import random

import tseytin_selector_sharing428 as sharing
import pell_fixed_affine_exponent52 as power

baseline=sharing.universal
word=baseline.word
loader=baseline.loader
execute=word.execute
exponent_name=baseline.exponent_name
INITIAL='c2_initial'
REMOVED={'c2_initial_product','c2_initial'}


def fused_coefficients():
    h=[8*c for c in loader.COEFFICIENTS]
    h[0]+=6*loader.DENOMINATOR
    assert h[2]==h[5]==0 and h[6]>0 and all(h[i]<0 for i in (0,1,3,4))
    return h


def program_parameter(S): return 8*loader.program_parameter(S)


def build(*,merge_units=True):
    assert type(merge_units) is bool
    w,p=sharing.build('word'),power.build()
    rows={n:(op,a,b) for n,op,a,b in w['source']}
    assert rows['c2_initial_product']==('*',8,'word')
    assert rows[INITIAL]==('+','c2_initial_product',6)
    assert {n for n,_,a,b in w['source'] if 'word' in (a,b)}=={'c2_initial_product'}
    assert {n for n,_,a,b in w['source'] if 'c2_initial_product' in (a,b)}=={INITIAL}
    source=[row for row in w['source'] if row[0] not in REMOVED]
    source += [(exponent_name(n),op,exponent_name(a),exponent_name(b))
               for n,op,a,b in p['source']]
    h=fused_coefficients(); q=loader.build()
    coefficients={'query_degree4':4,'query_degree3':3,'query_degree1':1,'query_numerator':0}
    def alias(v):
        if v=='Q':return exponent_name(v)
        return INITIAL if v=='word' else v
    for n,op,a,b in q['source']:
        source.append((n,op,alias(a),-h[coefficients[n]] if n in coefficients else alias(b)))
    ordinary=list(w['comparisons'][:-1])+list(q['comparisons'])
    W=w['unit_register'];P=exponent_name(p['unit_register']);unit=W
    comparisons=list(ordinary)
    if merge_units:
        unit='c2_power_unit';source.append((unit,'*',W,P))
    else:comparisons.append((P,1))
    comparisons.append((unit,1))
    parameters=['x','program_A']
    auxiliaries=[INITIAL]+list(w['auxiliaries'])+list(map(exponent_name,p['auxiliaries']))
    source=word.scale.sort_source(source,parameters+auxiliaries)
    word.scale.checked_source(source,parameters,auxiliaries)
    assert not any('word' in (a,b) for _,_,a,b in source)
    return word.scale.metadata(dict(source=source,parameters=parameters,auxiliaries=auxiliaries,
        comparisons=comparisons,ordinary_comparisons=ordinary,unit_register=unit,
        word_unit_register=W,power_unit_register=P,word_factors=list(w['unit_factors']),
        power_factors=list(map(exponent_name,p['unit_factors'])),merge_units=merge_units,
        interfaces=dict(input='x',program='program_A',initial=INITIAL,power=exponent_name('Q')),
        positive_integer_domain=True,
        program_recipe='program_A=8*((8**64-1)*8**17*enc8(S)+h6), with S the literal primary program word.',
        projection='On valid program slices, positive zeros accept exactly the enumerated positive set; the loader forces c2_initial=8*enc8(query)+6.'))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical fused composition required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    w=sharing.build('word');wd=sharing.degree_bound(w)
    # The old computed initial endpoint and its new supplied coordinate
    # both have degree1. Every retained word-source bound is identical.
    ws=[row for row in packet['source'] if row[0] in {n for n,_,_,_ in w['source']}]
    old=sharing.naive_degrees(w['source'],w['parameters']+w['auxiliaries'])
    new=sharing.naive_degrees(ws,[INITIAL]+w['auxiliaries'])
    assert all(new[n]==d for n,d in old.items() if n not in REMOVED|{'word'})
    pd=power.degrees()[0];pf=[pd[n] for n in power.FACTOR_NAMES]
    assert pf==[5,7,14,22,3,3]
    unit=wd['unit_degree_bound'];residual=max(wd['maximum_residual_degree_bound'],7)
    if packet['merge_units']:unit+=sum(pf)
    else:residual=max(residual,sum(pf))
    return dict(degree_upper_bound=2*max(unit,residual) if sum_of_squares else unit+2*residual,
        unit_degree_bound=unit,maximum_residual_degree_bound=residual,
        word_factor_degree_bounds=wd['factor_degree_bounds'],power_factor_degrees=pf,
        exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    c=Counter(op for _,op,_,_ in source)
    return dict(certificate={k:packet[k] for k in
        ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],
            additions_subtractions=c['+']+c['-'],output=out,
            **degree_bound(packet,sum_of_squares=sum_of_squares)))


def sign_filter():
    old=baseline.sign_filter();d=loader.DENOMINATOR;h=fused_coefficients();records=[]
    for rec in old['cases']:
        Q=rec['Q_residue'];R=8*rec['numerator_residue']
        assert 0<R<d
        assert sum(h[i]*pow(Q,i,d) for i in (0,1,3,4,6))%d==R
        records.append(dict(parity=rec['parity'],numerator_residue=R))
    return dict(parent_exact_certificate=old,fused_tail_coefficients=h,cases=records,
        identity='N_fused=8*N_old+6*d when program_A_fused=8*program_A_old; both wrong-branch residues are8 times the parent nonzero residue.')


def assignment_audit(cases=128):
    rng=random.Random(425652);w=sharing.build('word');p=power.build()
    forms=[(build(merge_units=m),s) for m in (False,True) for s in (False,True)]
    schedules=[polynomial_source(packet,sum_of_squares=s) for packet,s in forms]
    stripped=[row for row in w['source'] if row[0] not in REMOVED]
    totals=Counter();h=fused_coefficients()
    for case in range(cases):
        signed=case>=cases//2
        draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,5)
        values={n:draw() for n in forms[0][0]['parameters']+forms[0][0]['auxiliaries']}
        we=execute(stripped,{n:values[n] for n in [INITIAL]+w['auxiliaries']})
        pv={n:values[exponent_name(n)] for n in p['parameters']+p['auxiliaries']}
        pe=power.execute(p['source'],pv);pf=power.factors(pv)
        assert all(pe[n]==pf[n] for n in p['unit_factors'])
        W=prod(we[n] for n in w['unit_factors']);P=prod(pf.values())
        at=lambda a:we[a] if isinstance(a,str) else a
        R=[at(a)-at(b) for a,b in w['comparisons'][:-1]]
        Q=48*pv['x']+pv['delta'];A=values['program_A']
        R.append(A*Q**6+sum(h[i]*Q**i for i in (0,1,3,4))-loader.DENOMINATOR*values[INITIAL])
        S=sum(r*r for r in R)
        for (packet,sos),(source,out) in zip(forms,schedules):
            e=execute(source,values)
            assert all(e[n]==we[n] for n,_,_,_ in stripped)
            assert all(e[exponent_name(n)]==pe[n] for n,_,_,_ in p['source'])
            actual=[e[a]-(e[b] if isinstance(b,str) else b) for a,b in packet['ordinary_comparisons']]
            assert actual==R
            if packet['merge_units']:expected=(W*P-1)**2+S if sos else W*P*(1+S)-1
            else:expected=(W-1)**2+(P-1)**2+S if sos else W*(1+(P-1)**2+S)-1
            assert e[out]==expected
            totals['complete_parent_register_and_manual_output_identities']+=1
            totals['signed_output_identities']+=signed
    return dict(totals)


def endpoint_lift_audit(cases=96):
    rng=random.Random(425653);w=sharing.build('word');totals=Counter()
    for case in range(cases):
        signed=case>=cases//2
        draw=lambda:rng.randrange(-4,5) if signed else rng.randrange(1,5)
        base=build();v={n:draw() for n in base['parameters']+base['auxiliaries']}
        oldword=draw();oldA=draw();v[INITIAL]=8*oldword+6;v['program_A']=8*oldA
        old=execute(w['source'],{n:v[n] for n in w['auxiliaries']}|{'word':oldword})
        Q=48*v['x']+v['exp__delta'];oldquery=oldA*Q**6+sum(loader.COEFFICIENTS[i]*Q**i for i in (0,1,3,4))-loader.DENOMINATOR*oldword
        scalar=lambda a:old[a] if isinstance(a,str) else a
        residuals=[scalar(a)-scalar(b) for a,b in w['comparisons'][:-1]]
        S=sum(r*r for r in residuals);W=old[w['unit_register']]
        for merge in (False,True):
          packet=build(merge_units=merge)
          for sos in (False,True):
            source,out=polynomial_source(packet,sum_of_squares=sos);e=execute(source,v)
            assert all(e[n]==old[n] for n,_,_,_ in w['source'] if n not in REMOVED)
            assert e['query_numerator']-e['query_scaled_word']==8*oldquery
            P=e[packet['power_unit_register']]
            if merge:
                previous=(W*P-1)**2+S+oldquery**2 if sos else W*P*(1+S+oldquery**2)-1
                correction=63*oldquery**2*(1 if sos else W*P)
            else:
                previous=(W-1)**2+(P-1)**2+S+oldquery**2 if sos else W*(1+(P-1)**2+S+oldquery**2)-1
                correction=63*oldquery**2*(1 if sos else W)
            assert e[out]==previous+correction
            totals['endpoint_parent_register_and_complete_finalizer_corrections']+=1
            totals['signed_corrections']+=signed
    return dict(totals)


def query_audit():
    count=0;h=fused_coefficients();sf=sign_filter()
    for rank in (2,3,5):
      for relators in ((),((1,2,-1,-2),)):
        S=loader.program_word(rank,relators);A=program_parameter(S)
        for x in range(1,17):
            packet=build();v={n:1 for n in packet['parameters']+packet['auxiliaries']}
            qword=loader.encode(loader.query_word(S,x));v.update(x=x,program_A=A)
            v['exp__delta']=loader.B**x-48*x;v[INITIAL]=8*qword+6
            assert min(v.values())>0
            e=execute(packet['source'],v)
            assert e['exp__Q']==loader.B**x and e['query_numerator']==e['query_scaled_word']
            bad=loader.B**x//16
            assert (A*bad**6+sum(h[i]*bad**i for i in (0,1,3,4)))%loader.DENOMINATOR==sf['cases'][x%2]['numerator_residue']
            count+=1
    return dict(literal_program_input_and_negative_branch_cases=count,
        scope='Paid loader checks with placeholder other auxiliaries, not complete native/Pell zeros.')


def guards():
    p=build();bad=[dict(p,source=p['source'][:-1]),dict(p,auxiliaries=['word']+p['auxiliaries'][1:]),
        dict(p,comparisons=p['comparisons'][:-1]),dict(p,program_recipe='arbitrary positive A'),
        dict(p,interfaces={'initial':'word'})]
    for q in bad:
      for operation in (polynomial_source,degree_bound):
        try:operation(q)
        except AssertionError:pass
        else:raise AssertionError('altered canonical caller accepted')
    return 2*len(bad)


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        packet=build(merge_units=merge);source,out=polynomial_source(packet,sum_of_squares=sos)
        rec=ledger(packet,sum_of_squares=sos)
        assert len(source)==(425 if merge else 427)
        assert packet['operations']==(405 if merge else 404) and packet['equations']==(7 if merge else 8)
        assert packet['witnesses']==65
        baseline.closure(source,out,packet['parameters']+packet['auxiliaries'])
        rec.update(merge_units=merge,sum_of_squares=sos,source=source,output=out,
            parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],comparisons=packet['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    assert records[2]['polynomial']['multiplications']==199 and records[2]['polynomial']['additions_subtractions']==226
    assert [r['polynomial']['degree_upper_bound'] for r in records]==[5814,11352,5868,11460]
    return dict(status='PASS_TSEYTIN_UNIVERSAL425',forms=records,sign_filter=sign_filter(),
        assignments=assignment_audit(),endpoint_lifts=endpoint_lift_audit(),query_cases=query_audit(),
        rejected_mutations=guards(),scope='Complete universal source with ordinary positive input and one fixed positive program parameter. Exact zero equivalence on valid program slices, no identical polynomial or supplied-tuple bijection with440; no full giant Pell zero materialized.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['assignments']);print(result['endpoint_lifts'])
    print([(r['merge_units'],r['sum_of_squares'],r['polynomial']['operations'],r['polynomial']['degree_upper_bound']) for r in result['forms']])
