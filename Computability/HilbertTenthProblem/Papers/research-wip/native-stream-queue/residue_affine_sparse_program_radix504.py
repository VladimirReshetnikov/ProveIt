"""Two fixed program parameters trade one height addition for variable radix degree.

On valid slices C is dyadic, C>=64 and C>E.  The source counts C as an input,
not a free constant; ordinary x is unchanged.  No same-positive-zero claim.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import residue_affine_sparse_control_codes as parent

TABLE,PRIMES=parent.TABLE,parent.PRIMES
units,ps=parent.units,parent.ps
polynomial_source,ledger=parent.polynomial_source,parent.ledger
execute,at=parent.execute,parent.at


def rewrite(old):
    assert not old.get('program_radix_parameter')
    assert old==parent.build(old['form'],shared=old['shared']),'canonical default505 required'
    nodes={n:(op,a,b) for n,op,a,b in old['source']}
    h,B=old['interfaces']['h'],old['interfaces']['B']
    op,first,eta=nodes[h]
    assert op=='+' and eta=='height_slack' and nodes[first]==('+','program','input')
    assert nodes[B]==('*',64,h)
    assert {n for n,_,a,b in old['source'] if first in (a,b)}=={h}
    assert first not in parent.leaves([old['interfaces'],old['comparisons'],old.get('public_registers')])
    assert 'radix_program' not in set(nodes)|set(old['parameters']+old['auxiliaries'])
    rows=[]
    for n,op,a,b in old['source']:
        if n==first:continue
        if n==h:op,a,b='+','input','height_slack'
        if n==B:op,a,b='*','radix_program',h
        rows.append((n,op,a,b))
    parameters=['program','radix_program','input']
    packet=ps.metadata(dict(old,source=rows,parameters=parameters,
        interfaces=dict(old['interfaces'],radix_coefficient='radix_program'),
        radix_multiplier='radix_program',program_radix_parameter=True,
        fixed_program_parameters=['program','radix_program'],ordinary_input_parameter='input',
        program_radix_parent=old,deleted_height_register=first,
        height_definition='h=input+height_slack',
        valid_radix_recipe='C is a positive dyadic integer, C>=64 and C>program; default control plan only.',
        equivalence_scope='Accepted-input equivalence on valid fixed (program,C) slices, with fresh positive history/native extensions; no same-positive-zero or positive-inverse claim.'))
    ps.checked_source(rows,parameters,packet['auxiliaries'])
    assert packet['operations']==old['operations']-1
    assert packet['multiplications']==old['multiplications'] and packet['additions_subtractions']==old['additions_subtractions']-1
    assert packet['auxiliaries']==old['auxiliaries'] and packet['comparisons']==old['comparisons']
    assert packet['unit_factors']==old['unit_factors']
    for sos in (False,True):
        source,out=polynomial_source(packet,sum_of_squares=sos)
        assert parent.ancestors(source,[out])=={n for n,_,_,_ in source}
    return packet


def build(form='coupled',*,shared=True):
    return rewrite(parent.build(form,shared=shared))


def constant_parent(packet,C):
    """Formal specialization of the505 source at radix multiplier C.

    This helper is for exact polynomial comparison.  Signed integer C is
    allowed here; its semantic valid-slice hypotheses are stated separately.
    """
    assert type(C)is int
    old=packet['program_radix_parent'];B=old['interfaces']['B'];h=old['interfaces']['h']
    source=[(n,'*',C,h) if n==B else row for row in old['source'] for n in [row[0]]]
    return ps.metadata(dict(old,source=source,radix_multiplier=C))


def lift_to_constant_parent(values):
    result=dict(values);result.pop('radix_program')
    result['height_slack']=values['height_slack']-values['program']
    return result


def project_from_constant_parent(values,C):
    assert type(C)is int
    return dict(values,radix_program=C,height_slack=values['height_slack']+values['program'])


def valid_radix(program,C):
    return type(program)is int and program>0 and type(C)is int and C>=64 and C>program and C&(C-1)==0


def pack_path(packet,states,selected,input_value,C):
    """Pack a finite actual path using explicit fixed C; native auxiliaries unpaid here.

    Returned outer coordinates establish the hypotheses of the inherited
    native-extension theorem.  They do not materialize full Pell witnesses.
    """
    assert packet['program_radix_parameter'] and packet['radix_multiplier']=='radix_program'
    assert type(input_value)is int and input_value>0
    assert selected and len(states)==len(selected)+1 and states[0][0]==0 and states[-1][0]==len(TABLE)+1
    assert valid_radix(states[0][1],C)
    assert all(type(q)is int and type(v)is int and v>0 for q,v in states)
    assert all(type(i)is int and 0<=i<len(packet['edges']) for i in selected)
    assert len(selected)>input_value and selected[:input_value]==[0]*(input_value-1)+[1]
    assert all(i>=2 for i in selected[input_value:])
    W=[];R=[];S=[]
    for (q,value),(nxt,out),edge in zip(states,states[1:],selected):
        row=packet['edges'][edge];assert (q,nxt)==row[:2];prime=row[3]
        if row[2]=='I':
            w=value-1;r=s=0;assert out==prime*value
        elif row[2] in ('D','T'):
            assert value%prime==0;w=value//prime-1;r=s=0
            assert out==(value//prime if row[2]=='D' else value)
        else:
            w,rem=divmod(value,prime);assert 1<=rem<prime and out==value
            r=rem-1;s=prime-1-rem
        assert min(w,r,s)>=0;W.append(w);R.append(r);S.append(s)
    h=2
    while h<=max([input_value]+W+R+S):h*=2
    B=C*h;P=B**len(selected);J=(P-1)//(B-1)
    pack=lambda xs:sum(v*B**i for i,v in enumerate(xs))
    E=[pack([int(i==edge) for edge in selected]) for i in range(len(packet['edges']))]
    Z=[pack([w+1 if packet['edges'][edge][3]==prime else 0 for w,edge in zip(W,selected)]) for prime in packet['classes']]
    vd=[(packet['edges'][edge][3]-1)*(w+1) for w,edge in zip(W,selected)]
    Z += [pack([v if packet['edges'][edge][2]==kind else 0 for v,edge in zip(vd,selected)]) for kind in ('I','D')]
    V=pack(vd);beta=P-V-Z[-1]-Z[-2]-2
    assert beta>=((C-2*(max(PRIMES)-1))*h-1)*J-1>0
    L=E[0]+E[1];assert (L-input_value)%(B-1)==0
    result=dict(program=states[0][1],radix_program=C,input=input_value,
        final_payload=states[-1][1],height_slack=h-input_value,quotient_hat=pack(W)+1,
        remainder_hat=pack(R)+1,complement_hat=pack(S)+1,global_slack=beta,
        loader_quotient_hat=1+(L-input_value)//(B-1))
    result.update({f'edge{i}_hat':v+1 for i,v in enumerate(E)})
    result.update({f'product{i}_hat':v+1 for i,v in enumerate(Z)})
    assert min(result.values())>0
    return result


def identity_audit(packet,cases=32,seed=504123):
    rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-4,5) if signed else rng.randrange(1,7) for n in packet['parameters']+packet['auxiliaries']}
        old=constant_parent(packet,values['radix_program']);before=lift_to_constant_parent(values)
        assert project_from_constant_parent(before,values['radix_program'])==values
        for sos in (False,True):
            source,out=polynomial_source(packet,sum_of_squares=sos);bs,bo=polynomial_source(old,sum_of_squares=sos)
            a=execute(source,values);b=execute(bs,before)
            assert a[out]==b[bo]
            assert all(a[n]==b[n] for n,_,_,_ in packet['source'])
            assert all(at(a,x)-at(a,y)==at(b,x)-at(b,y) for x,y in packet['comparisons'])
            counts['complete_fixed_C_register_residual_finalizer_identities']+=1
            counts['signed_identities']+=signed
        counts['positive_offzero_nonpositive_parent_slacks']+=not signed and before['height_slack']<=0
        original={n:rng.randrange(1,8) for n in old['parameters']+old['auxiliaries']}
        projected=project_from_constant_parent(original,128)
        assert min(projected.values())>0 and lift_to_constant_parent(projected)==original
        counts['positive_constant_parent_forward_maps']+=1
    return dict(counts)


def outer_audit(packet):
    counts=Counter()
    for code in (0,1,2):
      program=3**code;C=64
      while C<=program:C*=2
      for x in (1,2,3,5):
        states,selected=parent.parent.parent.parent.payload_run(TABLE,program,x,PRIMES,limit=100)
        if states[-1][0]!=len(TABLE)+1:continue
        values=pack_path(packet,states,selected,x,C)
        rows=[row for row in packet['source'] if not row[0].startswith('native__') and row[0]!='sparse_all_units']
        env=execute(rows,values)
        assert all(at(env,a)==at(env,b) for a,b in packet['comparisons'][:4])
        assert env[packet['repunit_factor']]==1
        ports=packet['interfaces'];H,M,Z=[env[ports[k]] for k in ('joined_H','joined_M','joined_Z')]
        assert H&M==Z
        assert env[ports['B']]==C*env[ports['h']] and env[ports['P']]&(env[ports['P']]-1)==0
        assert env[ports['h']]==x+values['height_slack']
        counts['actual_halted_U21_outer_histories']+=1;counts['rows']+=len(selected)
    for h in range(2,18):
      for C in (64,128,256,512):
        B=C*h
        assert B-1>2*(max(PRIMES)-2) and B-1>2*(h-1) and B>63
        assert ((C-2*(max(PRIMES)-1))*h-1)-1>0
        counts['pretyping_bound_contexts']+=1
    return dict(counts)


def guard_audit():
    old=parent.build();bad=[]
    for field,value in (('radix_multiplier',128),('table',TABLE[:-1]),('source',old['source'][:-1]),('parameters',old['parameters']+['other'])):
        p=copy.deepcopy(old);p[field]=value;bad.append(p)
    plan=copy.deepcopy(parent.DEFAULT_PLAN);plan['target_basis']=[]
    bad.append(parent.build(plan=plan))
    rejected=0
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError,TypeError,ValueError):rejected+=1
        else:raise AssertionError('noncanonical505 accepted')
    for E,C in ((1,32),(64,64),(1,65),(1,64.0),(1,True),(0,64),(-1,64),(1,-64)):
        assert not valid_radix(E,C);rejected+=1
    assert valid_radix(1,64) and valid_radix(81,128)
    return dict(rejected_callers_or_radix_recipes=rejected)


def verify():
    records=[]
    for form in ('units','coupled'):
      for shared in (False,True):
        packet=build(form,shared=shared)
        records.append(dict(form=form,shared=shared,ledger=ledger(packet),checks=identity_audit(packet,seed=504000+len(records))))
    packet=build();source,out=polynomial_source(packet);default=ledger(packet)
    assert default['certificate']==dict(operations=484,multiplications=170,additions_subtractions=314,equations=7,witnesses=67)
    assert default['product']['operations']==504 and default['product']['multiplications']==177 and default['product']['additions_subtractions']==327
    assert default['product']['degree_upper_bound']==5160 and default['SOS']['degree_upper_bound']==10124
    return dict(status='PASS_SPARSE_TWO_PROGRAM_RADIX',default_ledger=default,
        parameters=packet['parameters'],fixed_program_parameters=packet['fixed_program_parameters'],
        valid_recipe=packet['valid_radix_recipe'],source=source,output=out,
        source_sha256=hashlib.sha256(json.dumps(source).encode()).hexdigest(),
        ledgers=records,outer_checks=outer_audit(packet),guards=guard_audit(),
        scope=packet['equivalence_scope'])


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default_ledger'])
