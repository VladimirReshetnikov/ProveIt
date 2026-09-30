"""Exact hidden-Boolean-carry FIFO64, affine controller70, and aligned72.

The symmetric-read specialization costs67. No universal simulation is claimed.
"""
import argparse
from collections import Counter, deque
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sympy as sp

import native_boolean_pair_fifo63 as paired
import input_bridge_boolean_ternary60 as boolean

FILTER = [('bc_slack', '+', 'F0', 1)]
CONTROL = [('bc_difference', '-', 'F2', 'F3'),
           ('bc_term0', '*', 'g0', 'F0'),
           ('bc_term1', '*', 'g1', 'F1'),
           ('bc_term2', '*', 'g2', 'bc_difference'),
           ('bc_sum01', '+', 'bc_term0', 'bc_term1'),
           ('bc_total', '+', 'bc_sum01', 'bc_term2')]
SYMMETRIC = [('bc_term0', '*', 'g0', 'F0'),
             ('bc_term1', '*', 'g1', 'F1'),
             ('bc_total', '+', 'bc_term0', 'bc_term1')]
ALIGN = [('bc_time_square', '*', 'time_root', 'time_root'),
         ('bc_width_square', '*', 'width_root', 'width_root')]


def source_check(controller=True, aligned=False, symmetric=False):
    assert controller or not (aligned or symmetric)
    base = paired.source_check(False)
    parameters = base['positive_parameters']
    auxiliaries = base['positive_auxiliaries'] + (['time_root','width_root'] if aligned else [])
    z = {name:sp.Symbol(name) for name in parameters+auxiliaries}
    fixed = {name:sp.Symbol(name) for name in ('g0','g1','g2','gap')}
    schedule = [tuple(row) for row in base['instructions']] + FILTER
    equations = [tuple(row['equality']) for row in base['sources']] + [('alpha','bc_slack')]
    polynomials = paired.independent_sources(z,False) + [z['alpha']-z['F0']-1]
    if controller:
        schedule += SYMMETRIC if symmetric else CONTROL
        equations += [('bc_total','gap')]
        polynomials += [fixed['g0']*z['F0']+fixed['g1']*z['F1']-fixed['gap']+
                        (0 if symmetric else fixed['g2']*(z['F2']-z['F3']))]
    if aligned:
        schedule += ALIGN
        equations += [('bc_time_square','q'),('bc_width_square','W')]
        polynomials += [z['time_root']**2-z['q'],z['width_root']**2-z['W']]
    env = boolean.prior.execute(schedule,dict(z,**fixed,n2=z['q']))
    u=2*z['r']+1+z['j']*z['c']
    correction=polynomials[8]*(u*u-z['y_aux']**2)
    records=[]
    for ix,((left,right),polynomial) in enumerate(zip(equations,polynomials)):
        adjust=correction if ix==9 else 0
        assert sp.expand(env[left]-env[right]-polynomial-adjust)==0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(polynomial)),
                            correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    extra=3 if symmetric else 6
    expected=64+extra*controller+2*aligned
    assert len(schedule)==expected
    assert counts['*']==32+(2 if symmetric else 3)*controller+2*aligned
    assert counts['+']+counts['-']==32+(1 if symmetric else 3)*controller
    assert len(equations)==len(polynomials)==19+controller+2*aligned
    assert len(parameters)+len(auxiliaries)-1==29+2*aligned
    h,u0,u1,v0,v1,cs,cf=sp.symbols('h u0 u1 v0 v1 cs cf')
    weighted=2*z['F0']+z['F1']+z['F2']+z['F3']
    full=2*cs+(h-2*cf)*weighted+2*(v0*z['F0']+v1*z['F1']+u0*z['F2']+u1*z['F3'])-2*cf
    reduced=(2*v0-2*u0-2*u1)*z['F0']+(2*v1-u0-u1)*z['F1']+(u0-u1)*(z['F2']-z['F3'])+2*cs-2*cf
    assert sp.expand(full.subs(h,2*cf-u0-u1)-reduced)==0
    if symmetric:
        assert sp.expand(reduced.subs(u1,u0)-((2*v0-4*u0)*z['F0']+(2*v1-2*u0)*z['F1']+2*cs-2*cf))==0
    return dict(operations=expected,multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'],equations=len(equations),
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                positive_existentials_excluding_x=len(parameters)+len(auxiliaries)-1,
                fixed_constants=({'g0':'2*v0-2*u0-2*u1','g1':'2*v1-u0-u1',
                                  'g2':'u0-u1','gap':'2*cf-2*cs',
                                  'endpoint_condition':'2*cf=h+u0+u1',
                                  'additional_condition':('u0=u1' if symmetric else None)} if controller else {}),
                alignment=('Both t and m are even' if aligned else None),
                instructions=[list(row) for row in schedule],sources=records,
                scope='Exact whole filtered finite-machine relation; no universal compiler')


def word(bits):
    return sum(bit*3**j for j,bit in enumerate(bits))


def digits(n,t):
    return tuple(n//3**j%3 for j in range(t))


def hidden_step(e,label):
    a0,a1,d0,d1=label
    n=e+2*a0+a1+d0+d1-2
    return n//3 if n%3==0 and 0<=n//3<=1 else None


LABELS=list(product((0,1),repeat=4))
EDGES={e:[(label,hidden_step(e,label)) for label in LABELS if hidden_step(e,label) is not None] for e in (0,1)}


def filter_checks():
    cases=admitted=positive=0
    for t in range(1,5):
        q=3**t
        values=[word(bits) for bits in product((0,1),repeat=t)]
        for fields in product(values,repeat=4):
            algebraic=2*fields[0]+sum(fields[1:])==q-1
            e=0
            for j in range(t):
                e=hidden_step(e,tuple(f//3**j%3 for f in fields))
                if e is None:break
            path=e==0
            assert algebraic==path
            if algebraic:
                assert sum(fields)<q and q-sum(fields)==fields[0]+1
                admitted+=1
                positive+=min(fields)>0
            cases+=1
    return dict(boolean_field_tuples=cases,admitted=admitted,positive_admitted=positive,
                lengths=[1,4],zero_fields_included=True,
                edges=[dict(carry=e,label_append_then_read=list(label),next_carry=nxt)
                       for e in (0,1) for label,nxt in EDGES[e]])


def hidden_words(t,e=0,prefix=()):
    if t==0:
        if e==0:yield prefix
        return
    for label,nxt in EDGES[e]:
        yield from hidden_words(t-1,nxt,prefix+(label,))


def carry_checks():
    # u0,u1,v0,v1,h,cs,cf, each with the forced endpoint identity.
    configs=[(-1,1,2,1,0,0,0),(1,1,-1,13,-2,0,0),
             (3,-2,5,-4,3,-1,2),(0,0,0,0,0,0,0)]
    cases=admitted=0
    for t in range(1,6):
        q,H=3**t,(3**t-1)//2
        for labels in hidden_words(t):
            fields=[word(row[i] for row in labels) for i in range(4)]
            for u0,u1,v0,v1,h,cs,cf in configs:
                assert 2*cf==h+u0+u1
                reduced=((2*v0-2*u0-2*u1)*fields[0]+(2*v1-u0-u1)*fields[1]+
                         (u0-u1)*(fields[2]-fields[3])==2*(cf-cs))
                full=cs+h*H+v0*fields[0]+v1*fields[1]+u0*fields[2]+u1*fields[3]==q*cf
                c=cs;integral=True
                for a0,a1,d0,d1 in labels:
                    n=c+h+v0*a0+v1*a1+u0*d0+u1*d1
                    if n%3:integral=False;break
                    c=n//3
                actual=integral and c==cf
                assert reduced==full==actual
                cases+=1;admitted+=actual
    return dict(hidden_words_and_controller_configs=cases,admitted=admitted,
                maximum_length=5,configs=[list(row) for row in configs],
                scope='Exact local/global identity; FIFO not imposed in this standalone test')


def positive_fixture():
    q,W,x=27,3,1;fields=[4,1,13,4];initial=[1,1]
    labels=list(zip(*(digits(f,3) for f in fields)))
    hidden=[0]
    for label in labels:hidden.append(hidden_step(hidden[-1],label))
    assert hidden==[0,1,1,0]
    assert paired.direct_pair(initial,fields,1,3)
    assert all(boolean.native_boolean(f,3) for f in fields)
    assert sum(fields)%2==0 and q-sum(fields)==fields[0]+1==5
    controllers=[]
    for u0,u1,v0,v1,h in [(-1,1,2,1,0),(1,1,-1,13,-2)]:
        c=0;path=[c]
        for a0,a1,d0,d1 in labels:
            n=c+h+u0*d0+u1*d1+v0*a0+v1*a1
            assert n%3==0
            c=n//3;path.append(c)
        assert c==0
        controllers.append(dict(read=[u0,u1],append=[v0,v1],h=h,cs=0,cf=0,carries=path))
    return dict(x=x,W=W,q=q,initial=initial,fields=fields,alpha=5,width_beta=1,L=9,
                hidden_carries=hidden,labels_append_then_read=[list(row) for row in labels],
                controllers=controllers,
                positive_kernel_extension='Inherited exact Boolean55 converse; large Pell coordinates not materialized')


def terminal_checks():
    configs=[(-1,1,2,1,0,0),(1,1,-1,13,-2,0),(3,2,5,4,-2,0),
             (-2,1,4,-3,1,1),(1,0,3,2,0,0),(0,0,0,0,0,0)]
    states=endpoints=wrong=0;aligned_example=None
    for m in range(1,4):
        W=3**m;values=[word(bits) for bits in product((0,1),repeat=m)]
        for x in (1,2,3):
            if 2*x>=W:continue
            initials=[(I,2*x-I) for I in values if I>0 and 2*x-I>0 and 2*x-I in values]
            for u0,u1,v0,v1,h,cs in configs:
                G=abs(h)+abs(u0)+abs(u1)+abs(v0)+abs(v1)
                C=max(abs(cs),(G+1)//2);B=2*C+abs(h+u0+u1)
                for initial in initials:
                    # Time parity is retained so square alignment is tested exactly.
                    first=(*initial,0,cs,0,0)
                    seen={first:(0,(),())};pending=deque([first])
                    while pending:
                        n0,n1,e,c,mask,parity=state=pending.popleft()
                        t,tail,path=seen[state];states+=1
                        if n0==n1==e==0 and mask==15:
                            endpoints+=1
                            assert t>m
                            assert all(label[:2]==(0,0) for label in tail)
                            assert all(label==(0,0,1,1) for label in tail[1:])
                            delta=2*c-h-u0-u1
                            assert (W//3)*abs(delta)<=B
                            if delta:
                                assert 2*x<W<=3*B;wrong+=1
                            if m%2==0 and parity==0 and c==0 and aligned_example is None:
                                fields=[word(row[i] for row in path) for i in range(4)]
                                assert sum(fields)%2==0 and min(fields)>0
                                assert 2*fields[0]+sum(fields[1:])==3**t-1
                                aligned_example=dict(x=x,m=m,t=t,initial=list(initial),fields=fields,
                                    hidden_end=e,controller=dict(read=[u0,u1],append=[v0,v1],h=h,cs=cs,cf=c))
                        d0,d1=n0%3,n1%3
                        for a0,a1 in product((0,1),repeat=2):
                            label=(a0,a1,d0,d1);ee=hidden_step(e,label)
                            if ee is None:continue
                            numer=c+h+u0*d0+u1*d1+v0*a0+v1*a1
                            if numer%3:continue
                            cc=numer//3;assert abs(cc)<=C
                            mm=mask|sum(bit<<i for i,bit in enumerate(label))
                            nxt=(n0//3+(W//3)*a0,n1//3+(W//3)*a1,ee,cc,mm,1-parity)
                            if nxt not in seen:
                                seen[nxt]=(t+1,(tail+(label,))[-m:],path+(label,));pending.append(nxt)
    assert endpoints and wrong and aligned_example
    assert 2*aligned_example['controller']['cf']==aligned_example['controller']['h']+sum(aligned_example['controller']['read'])
    return dict(reachable_configurations=states,positive_track_zero_endpoints=endpoints,
                wrong_endpoint_examples=wrong,aligned_positive_example=aligned_example,
                widths_m=[1,3],inputs=[1,2,3],configs=[list(row) for row in configs],
                scope='Whole finite graph reachability; mathematical tail proof applies to all lengths')


def input_omission_checks():
    initial_words=steps=even_positive_splits=0
    alphabet=((0,0),(1,0),(0,1))
    for m in range(1,6):
        W=3**m
        for queue in product(alphabet,repeat=m):
            initial_words+=1
            I0,I1=(word(row[i] for row in queue) for i in (0,1))
            if I0>0 and I1>0 and (I0+I1)%2==0:
                even_positive_splits+=1
                assert I0+I1<W
            seen=set();current=queue
            while current not in seen:
                seen.add(current)
                d0,d1=current[0]
                choices=[(label,nxt) for label,nxt in EDGES[0] if label[2:]==(d0,d1)]
                assert len(choices)==1
                label,nxt=choices[0]
                assert nxt==0 and label[:2] in ((1,0),(0,1))
                current=current[1:]+(label[:2],)
                assert any(a or b for a,b in current)
                assert all((a,b)!=(1,1) for a,b in current)
                steps+=1
    assert word((1,1))==4 and paired.positive_split(4) in ((1,3),(3,1))
    return dict(no11_initial_physical_words=initial_words,orbit_steps=steps,
                positive_even_sum_splits=even_positive_splits,widths_m=[1,5],
                omitted_example=dict(x=2,ordinary_sum=4,ternary_low_first=[1,1]),
                scope='Exact closed e0/no11 alphabet always appends a nonzero symbol; all widths excluded parametrically')


def alignment_checks():
    for exponent in range(1,101):
        value=3**exponent
        assert (isqrt(value)**2==value)==(exponent%2==0)
    return dict(exponents_checked=100,statement='Positive square root of a power of3 iff exponent even')


def verify():
    return dict(status='PASS_BOOLEAN_CARRY_FIFO64_67_70_72',
                sources=dict(filter64=source_check(False),controller70=source_check(),
                             symmetric67=source_check(symmetric=True),aligned72=source_check(aligned=True)),
                filter=filter_checks(),carry=carry_checks(),positive_fixture=positive_fixture(),
                terminal=terminal_checks(),alignment=alignment_checks(),input_omissions=input_omission_checks(),
                scope='Exact finite-machine components; no ordinary-input universal simulation',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key!='sources'},indent=2))
