#!/usr/bin/env python3
"""Three paid operations saved by positive program-frame reparameterization.

Positive auxiliary zero sets agree at corresponding positive program triples.
Arbitrary new triples need not decode to old triples. Off-zero source equality
is stated only after the explicit initial-value override recorded below.
"""
# Public and inherited canonical guards deliberately use assertions.
# Refuse optimized execution before importing any guarded dependency.
if not __debug__:
    raise RuntimeError('gpcp_program_frame741 requires enabled assertions; Python -O/-OO is unsupported')

import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import random

import gpcp_history_computed_fields744 as parent

PARENT_SHA256='da3ec5d08068a9fcfa783f1ed0b0d97b2f2aa5b33cc63c218f003716b347f1ef'
OLD_PROGRAM=('program_prefix','program_suffix_scale','program_suffix_value')
NEW_PROGRAM=('program_repunit_coefficient','program_bit_coefficient','program_offset')
FRAME=('zero_blocks','one_correction','encoded_body','framed_prefix','framed_body','framed_scaled','input_bottom')
PRIVATE=FRAME[:-1]
NEW_ROWS=('frame_repunit_term','frame_bit_term','frame_partial','input_bottom')
FLAGS=('inline_initial','and_bounds','geometry_bounds')
PRIMES=parent.PRIMES
PREFIXES=parent.PREFIXES
execute=parent.execute
exact_equal=parent.exact_equal


def guard():
    assert hashlib.sha256(Path(parent.__file__).read_bytes()).hexdigest()==PARENT_SHA256
    parent.parent_hash_guard()


def flags(*values):
    assert len(values)==3 and all(type(v) is bool for v in values)
    return values


@lru_cache(None)
def _parent(inline,ands,geo):
    return parent.build(inline_initial=inline,and_bounds=ands,geometry_bounds=geo)


def canonical_parent(inline_initial=True,and_bounds=True,geometry_bounds=True):
    key=flags(inline_initial,and_bounds,geometry_bounds);guard()
    return deepcopy(_parent(*key))


def rewrite(old):
    assert type(old) is dict
    key=flags(*(old.get(k) for k in FLAGS));guard()
    assert exact_equal(old,_parent(*key)), 'complete exact-type canonical744 parent required'
    by={n:(o,a,b) for n,o,a,b in old['source']}
    assert len(by)==len(old['source'])
    c0,c1=old['block_values'];M=(1<<old['width'])-1;delta=c1-c0
    assert old['width']==64 and 0<c0<c1<1<<64
    expected={
        'zero_blocks':('*',c0,'input_repunit'),
        'one_correction':('*',delta,'z'),
        'encoded_body':('+','zero_blocks','one_correction'),
        'framed_prefix':('*','program_prefix','Q'),
        'framed_body':('+','framed_prefix','encoded_body'),
        'framed_scaled':('*','program_suffix_scale','framed_body'),
        'input_bottom':('+','framed_scaled','program_suffix_value'),
        'input_repunit_scaled':('*',M,'input_repunit'),
        'input_repunit_power':('+','input_repunit_scaled',1),
    }
    assert all(by.get(n)==row for n,row in expected.items())
    assert old['comparisons'].count(('input_repunit_power','Q'))==1
    users=lambda s:{n for n,o,a,b in old['source'] if s in (a,b)}
    wanted={
        'zero_blocks':{'encoded_body'},'one_correction':{'encoded_body'},
        'encoded_body':{'framed_body'},'framed_prefix':{'framed_body'},
        'framed_body':{'framed_scaled'},'framed_scaled':{'input_bottom'},
        'program_prefix':{'framed_prefix'},'program_suffix_scale':{'framed_scaled'},
        'program_suffix_value':{'input_bottom'},
    }
    assert all(users(n)==u for n,u in wanted.items())
    assert not set(PRIVATE+OLD_PROGRAM)&parent.degrees_parent.leaves(old['comparisons'])
    # The interface input_bottom is intentionally shared with the full history.
    input_users=users('input_bottom')
    assert input_users==({'hist__height_sum__0','hist__V_lhs__316'} if key[0] else set())
    assert (('input_bottom','Vinitial') in old['comparisons']) is (not key[0])
    active={k:old[k] for k in parent.degrees_parent.ACTIVE+('history_packet',)
            if k not in ('parameters','comparisons')}
    assert not set(PRIVATE+OLD_PROGRAM)&parent.degrees_parent.leaves(active)
    rows=[r for r in old['source'] if r[0] not in FRAME]
    rows += [('frame_repunit_term','*',NEW_PROGRAM[0],'input_repunit'),
             ('frame_bit_term','*',NEW_PROGRAM[1],'z'),
             ('frame_partial','+','frame_repunit_term','frame_bit_term'),
             ('input_bottom','+','frame_partial',NEW_PROGRAM[2])]
    params=['x']+list(NEW_PROGRAM)
    assert old['parameters']==['x']+list(OLD_PROGRAM)
    rows=parent.degrees_parent.sorted_source(rows,params+old['auxiliaries'])
    count=Counter(o for n,o,a,b in rows)
    p=parent.parent.parent.compact_parent(old)
    # Ancestral coordinate projection claims are not current741 claims.
    p.update(source=rows,parameters=params,operations=len(rows),multiplications=count['*'],
             additions_subtractions=count['+']+count['-'],equations=old['equations'],
             witnesses=old['witnesses'],parent_stage=744,parent_sha256=PARENT_SHA256,
             history_computed_fields=True,recoder_computed_fields=False,
             computed_interface=deepcopy(old['computed_interface']),
             frame_reparameterized=True,frame_constants=dict(width=64,modulus=M,c0=c0,delta=delta),
             frame_privacy=dict(private_consumers={n:sorted(u) for n,u in wanted.items()},
                                input_bottom_consumers=sorted(input_users),
                                supplied_initial_comparison=not key[0]),
             erased_frame_registers=list(PRIVATE),program_parameters=list(NEW_PROGRAM),
             parent_program_parameters=list(OLD_PROGRAM),
             program_map=dict(zip(NEW_PROGRAM,('a*(p*M+c0)','a*delta','a*p+b'))),
             signed_frame_difference='Vold-Vnew=a*p*(Q-M*input_repunit-1)',
             same_auxiliary_coordinates=True,same_arbitrary_parameter_zero_set=False,
             positive_relation_scope='For every positive old program triple (p,a,b), its positive image (a*(p*M+c0),a*delta,a*p+b) has exactly the same auxiliary positive zeros. New triples outside this image have no claimed old program interpretation.',
             universal_scope='Every valid old program slice yields a valid new slice with unchanged ordinary positive input and every supplied auxiliary. This is not a new87-operation bound.',
             supplied_domain='positive integers; signed integers accepted only for formal algebra')
    assert len(rows)==old['operations']-3
    assert p['multiplications']==old['multiplications']-2
    assert p['additions_subtractions']==old['additions_subtractions']-1
    assert p['comparisons']==old['comparisons'] and p['unit_factors']==old['unit_factors']
    assert p['auxiliaries']==old['auxiliaries']
    assert not set(PRIVATE+OLD_PROGRAM)&parent.degrees_parent.leaves({k:p[k] for k in parent.degrees_parent.ACTIVE+('history_packet',)})
    return p


@lru_cache(None)
def _build(inline,ands,geo):
    return rewrite(_parent(inline,ands,geo))


def build(*,inline_initial=True,and_bounds=True,geometry_bounds=True):
    key=flags(inline_initial,and_bounds,geometry_bounds);guard()
    return deepcopy(_build(*key))


def checked(packet):
    assert type(packet) is dict
    key=flags(*(packet.get(k) for k in FLAGS));guard()
    assert exact_equal(packet,_build(*key)), 'complete exact-type canonical741 packet required'


def polynomial_source(packet=None):
    if packet is None:packet=build()
    checked(packet)
    return parent.parent.parent.finalizer.polynomial_source(packet)


def checked_values(packet,values,*,parent_values=False):
    checked(packet);assert type(parent_values) is bool
    params=['x']+list(OLD_PROGRAM) if parent_values else packet['parameters']
    assert type(values) is dict and set(values)==set(params+packet['auxiliaries'])
    assert all(type(n) is str and type(v) is int for n,v in values.items())


def _program_image(packet,p,a,b):
    c=packet['frame_constants']
    return dict(zip(NEW_PROGRAM,(a*(p*c['modulus']+c['c0']),a*c['delta'],a*p+b)))


def transform_program(packet,values):
    checked(packet)
    assert type(values) is dict and set(values)==set(OLD_PROGRAM)
    assert all(type(k) is str and type(v) is int and v>0 for k,v in values.items())
    return _program_image(packet,*(values[n] for n in OLD_PROGRAM))


def decode_program(packet,values):
    """Proof/API utility, not a gate in the Diophantine evaluator."""
    checked(packet)
    assert type(values) is dict and set(values)==set(NEW_PROGRAM)
    assert all(type(k) is str and type(v) is int and v>0 for k,v in values.items())
    A,B,C=(values[n] for n in NEW_PROGRAM);c=packet['frame_constants']
    assert B%c['delta']==0,'new triple is outside old positive image'
    a=B//c['delta'];assert a>0 and A%a==0
    numerator=A//a-c['c0'];assert numerator%c['modulus']==0
    p=numerator//c['modulus'];b=C-a*p
    assert p>0 and b>0,'new triple is outside old positive image'
    result=dict(zip(OLD_PROGRAM,(p,a,b)))
    assert transform_program(packet,result)==values
    return result


def map_assignment(packet,values):
    """Formal signed parameter map; every auxiliary and x is retained."""
    checked_values(packet,values,parent_values=True)
    answer={n:v for n,v in values.items() if n not in OLD_PROGRAM}
    answer.update(_program_image(packet,*(values[n] for n in OLD_PROGRAM)))
    return answer


def evaluate(packet,values):
    checked_values(packet,values);rows,out=polynomial_source(packet)
    return execute(rows,values)[out]


def _override(rows,values,initial):
    """Explicit interface experiment, not evaluation of the original polynomial."""
    e=dict(values)
    for n,o,a,b in rows:
        if n=='input_bottom':e[n]=initial;continue
        a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
        e[n]=a*b if o=='*' else a+b if o=='+' else a-b
    return e


def interface_identity(packet,values):
    """All signed child tuples; compare parent after initial-interface override."""
    checked_values(packet,values)
    old=canonical_parent(*(packet[k] for k in FLAGS))
    new_rows,new_out=polynomial_source(packet);old_rows,old_out=parent.polynomial_source(old)
    env=execute(new_rows,values)
    previous={n:v for n,v in values.items() if n not in NEW_PROGRAM}
    previous.update(dict.fromkeys(OLD_PROGRAM,1))
    override=_override(old_rows,previous,env['input_bottom'])
    common=set(n for n,o,a,b in new_rows)&set(n for n,o,a,b in old_rows)
    assert all(env[n]==override[n] for n in common)
    assert env[new_out]==override[old_out]
    return dict(child_output=env[new_out],parent_with_overridden_initial_output=override[old_out],
                overridden_initial_value=env['input_bottom'],compared_common_registers=len(common))


def parameter_correction(packet,values):
    """Exact signed change after the formal parameter map, with no claimed cancellation."""
    checked_values(packet,values,parent_values=True)
    old=canonical_parent(*(packet[k] for k in FLAGS))
    old_rows,old_out=parent.polynomial_source(old);new_rows,new_out=polynomial_source(packet)
    before=execute(old_rows,values);mapped=map_assignment(packet,values);after=execute(new_rows,mapped)
    p,a,b=(values[n] for n in OLD_PROGRAM);M=packet['frame_constants']['modulus']
    repunit=before['Q']-M*values['input_repunit']-1
    shift=a*p*repunit
    assert before['input_bottom']-after['input_bottom']==shift
    override=_override(new_rows,mapped,after['input_bottom']+shift)
    common=set(n for n,o,a,b in new_rows)&set(n for n,o,a,b in old_rows)
    assert all(before[n]==override[n] for n in common)
    assert before[old_out]==override[new_out]
    if repunit==0:assert before[old_out]==after[new_out]
    return dict(parent_output=before[old_out],mapped_child_output=after[new_out],
                child_with_corrected_initial_output=override[new_out],
                repunit_residual=repunit,initial_correction=shift,
                full_output_difference=before[old_out]-after[new_out])


def degree_dictionary(packet=None):
    if packet is None:packet=build()
    rows,_=polynomial_source(packet)
    return parent.degrees_parent.raw_degrees(dict(packet,source=rows))


def leading_audit(packet,prime):
    assert type(prime) is int and prime in PRIMES
    rows,out=polynomial_source(packet);degree=degree_dictionary(packet)
    top={n:i+2 for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
    for pre in PREFIXES:top[pre+'tau_gap']=top[pre+'eta']=top[pre+'zeta']=1
    assignment=dict(top)
    for n,o,a,b in rows:
        da=degree[a] if isinstance(a,str) else 0;db=degree[b] if isinstance(b,str) else 0
        va=top[a] if isinstance(a,str) else a;vb=top[b] if isinstance(b,str) else b
        top[n]=(va*vb if o=='*' else (va if da==degree[n] else 0)+(1 if o=='+' else -1)*(vb if db==degree[n] else 0))%prime
        for pre in PREFIXES:
            if n!=pre+'R15':continue
            d=lambda x:degree[pre+x]
            assert degree[n]==d('cam2')+d('gam')>max(2*d('wn2'),d('wn2')+d('cam2'),d('wn2')+d('gam'),2*d('gam'),d('a4m5')+2*d('R10a'))
            top[n]=2*top[pre+'cam2']*top[pre+'gam']%prime
    assert top[out] and all(top[n] for n in packet['unit_factors'])
    return dict(prime=prime,input_top_assignment=assignment,output_leader_value=top[out],
                factor_leader_values={f:top[f] for f in packet['unit_factors']})


def degree_audit(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);degree=degree_dictionary(packet)
    return dict(exact_degree=degree[out],formal_degree_bound=degree[out],
                initial_value_degree=degree['input_bottom'],
                leading_certificates=[leading_audit(packet,p) for p in PRIMES],
                scope='Formal degree in independent new program parameters and positive witnesses; before fixed-language specialization.')


def ledger(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);c=Counter(o for n,o,a,b in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
                polynomial=dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-']),degree=degree_audit(packet))


def forms():yield from product((False,True),repeat=3)


def guards():
    count=0;copies=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,TypeError,ValueError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for key in forms():
        p=build(**dict(zip(FLAGS,key)));old=canonical_parent(*key)
        vals={n:1 for n in p['parameters']+p['auxiliaries']}
        oldvals={n:1 for n in old['parameters']+old['auxiliaries']}
        for field,value in [('source',p['source'][:-1]),('comparisons',[]),('unit_factors',[]),
                            ('program_map',{}),('frame_privacy',{}),('history_packet',{}),
                            ('same_arbitrary_parameter_zero_set',True),('parent_stage',True)]:
            bad=deepcopy(p);bad[field]=value
            for api in (checked,polynomial_source,degree_audit,ledger):reject(lambda api=api,bad=bad:api(bad))
        for value in (1.0,True):
            bad=deepcopy(p)
            i=next(i for i,row in enumerate(bad['source']) if any(type(x) is int and x==1 for x in row[2:]))
            row=list(bad['source'][i]);j=next(j for j in (2,3) if type(row[j]) is int and row[j]==1)
            row[j]=value;bad['source'][i]=tuple(row)
            for api in (checked,polynomial_source,ledger):reject(lambda api=api,bad=bad:api(bad))
            badvalues=dict(vals,x=value)
            for api in (evaluate,interface_identity):reject(lambda api=api,badvalues=badvalues:api(p,badvalues))
            reject(lambda value=value:map_assignment(p,dict(oldvals,x=value)))
            reject(lambda value=value:parameter_correction(p,dict(oldvals,x=value)))
            badprogram=dict.fromkeys(OLD_PROGRAM,1);badprogram[OLD_PROGRAM[0]]=value
            reject(lambda badprogram=badprogram:transform_program(p,badprogram))
            badprogram=dict.fromkeys(NEW_PROGRAM,1);badprogram[NEW_PROGRAM[0]]=value
            reject(lambda badprogram=badprogram:decode_program(p,badprogram))
        for changed in (dict(vals,unexpected=1),{n:v for n,v in vals.items() if n!='x'}):
            reject(lambda changed=changed:evaluate(p,changed))
        reject(lambda:decode_program(p,dict.fromkeys(NEW_PROGRAM,1)))
        for field in ('source','parameters','comparisons','auxiliaries'):
            bad=deepcopy(old);bad[field]=bad[field][:-1];reject(lambda bad=bad:rewrite(bad))
        huge=dict(vals,x=10**400);bad=deepcopy(p)
        i=next(i for i,row in enumerate(bad['source']) if row[0]=='input_repunit_scaled')
        row=list(bad['source'][i]);row[2]=float(row[2]);bad['source'][i]=tuple(row)
        reject(lambda:evaluate(bad,huge))
        # Public return values must never mutate either canonical cache.
        pristine=build(**dict(zip(FLAGS,key)))
        p['source'].clear();p['frame_constants']['c0']=0;p['history_packet']['groups_U'].clear()
        assert exact_equal(build(**dict(zip(FLAGS,key))),pristine)
        before=canonical_parent(*key);old['source'].clear();old['history_packet']['groups_U'].clear()
        assert exact_equal(canonical_parent(*key),before)
        copies+=2
    for bad in (0,1,1.0,None,'yes'):
        for index in range(3):
            options=[True]*3;options[index]=bad
            reject(lambda options=options:build(**dict(zip(FLAGS,options))))
            reject(lambda options=options:canonical_parent(*options))
    return dict(rejected_callers=count,public_cache_copy_checks=copies)


def verify():
    records=[];counts=Counter();digest=hashlib.sha256();rng=random.Random(741744)
    for key in forms():
        p=build(**dict(zip(FLAGS,key)));old=canonical_parent(*key)
        rows,out=polynomial_source(p);past,_=parent.polynomial_source(old)
        record=ledger(p)
        assert len(rows)==len(past)-3
        record.update(dict(zip(FLAGS,key)),source=rows,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                      comparisons=p['comparisons'],unit_factors=p['unit_factors'],frame_constants=p['frame_constants'],frame_privacy=p['frame_privacy'])
        records.append(record)
        by={n:(a,b) for n,o,a,b in rows};seen=set();todo=[out]
        while todo:
            n=todo.pop()
            if isinstance(n,str) and n in by and n not in seen:seen.add(n);todo.extend(by[n])
        assert seen==by.keys()
        assert set(p['parameters']+p['auxiliaries'])<=parent.degrees_parent.leaves(rows)
        for case in range(12):
            signed=case>=6
            vals={n:rng.randrange(-2,3) if signed else rng.randrange(1,3) for n in p['parameters']+p['auxiliaries']}
            result=interface_identity(p,vals)
            digest.update(str(result['child_output']%PRIMES[0]).encode());counts['complete_interface_override_identities']+=1
            oldvals={n:rng.randrange(-2,3) if signed else rng.randrange(1,3) for n in old['parameters']+old['auxiliaries']}
            if case in (8,9):oldvals.update(x=2,input_slack=-1,input_repunit=0)
            result=parameter_correction(p,oldvals)
            digest.update(str(result['full_output_difference']%PRIMES[0]).encode())
            counts['complete_parameter_corrections']+=1;counts['signed_cases']+=signed
            counts['zero_repunit_actual_full_equalities']+=result['repunit_residual']==0
            counts['nonzero_actual_polynomial_differences']+=result['full_output_difference']!=0
        for triple in product((1,2,5),repeat=3):
            oldprog=dict(zip(OLD_PROGRAM,triple));image=transform_program(p,oldprog)
            assert decode_program(p,image)==oldprog and min(image.values())>0
            counts['positive_program_map_roundtrips']+=1
    return dict(status='PASS_GPCP_PROGRAM_FRAME741',parent_source_sha256=PARENT_SHA256,
                source_file_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                forms=records,checks=dict(counts),guards=guards(),result_digest=digest.hexdigest(),
                scope='Language-preserving positive program-parameter transformation; no all-new-parameter interpretation, no complete positive Pell fixture, no smaller87 bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['checks'])
    print([(tuple(r[k] for k in FLAGS),r['polynomial'],r['degree']['exact_degree']) for r in result['forms']])
