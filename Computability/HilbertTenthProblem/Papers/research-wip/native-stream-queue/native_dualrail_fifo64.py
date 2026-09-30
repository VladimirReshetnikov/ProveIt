"""Exact64 dual-rail FIFO: aggregate bounds and ordinary initial queue6x."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_dualrail_fifo67 as prior

selector=prior.selector
PACKING=[row for row in prior.base.prior.OUTER
         if not row[0].startswith('bound') and row[0]!='even_r']
PREFIX=PACKING+[('packed_bound','+','r','alphaP'),('twice_H','-','q',1)]
FIFO=[(name,op,6 if name=='initial' else left,right)
      for name,op,left,right in prior.EXTRA66]
BOUNDS=[('append_bound','+','append_sum','alphaA'),('read_bound','+','read_sum','alphaD')]


def source_check():
    parameters=['x','W','q','F0','F1','F2','F3']
    auxiliaries=selector.CORE_NAMES+['alphaP','alphaA','alphaD','beta','L']
    z={name:sp.Symbol(name) for name in parameters+auxiliaries}
    schedule=PREFIX+selector.CORE+FIFO+BOUNDS
    env=selector.execute(schedule,z)
    equalities=[('r','packed'),('packed_bound','n2'),('append_bound','q'),('read_bound','q')]
    equalities+=selector.kernel.EQUALITIES[1:]
    equalities+=[('read_sum','transport'),('width_bound','W'),('q','length_product')]
    old=prior.base.prior.independent_sources(dict(z,nu=sp.Integer(0),
            **{f'alpha{i}':sp.Integer(0) for i in range(4)}),False)
    q=z['q'];A=z['F0']+z['F1']-q+1;D=z['F2']+z['F3']-q+1
    sources=[old[4],z['r']+z['alphaP']-q**4,A+z['alphaA']-q,D+z['alphaD']-q]
    sources+=old[6:]
    sources+=[D-6*z['x']-z['W']*A,6*z['x']+z['beta']-z['W'],q-z['W']*z['L']]
    u=2*z['r']+1+z['j']*z['c'];correction=sources[11]*(u*u-z['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if index==12 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,index
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==64 and counts['*']==33 and counts['+']+counts['-']==31
    assert len(equalities)==len(sources)==17 and len(auxiliaries)==22
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=64,multiplications=33,additions_subtractions=31,equations=17,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records,
                initial_queue='6x',bounds='packed r<q^4, scalar append A<q, scalar read D<q')


def field_carry_scan():
    rows=[]
    for t in range(1,4):
        q=3**t;H=(q-1)//2;scale=q**4
        pairs=[(f,g) for f in range(1,2*q-2) for g in range(1,2*q-1-f)]
        checked=valuation_accepted=native=boundary=full_fifo=0
        for (F0,F1),(F2,F3) in product(pairs,repeat=2):
            fields=(F0,F1,F2,F3);P=prior.base.prior.packed(fields,q)
            if P>=scale:continue
            checked+=1
            if selector.valuation(P)<4*t:continue
            valuation_accepted+=1
            carry=0;chunks=[];carries=[]
            for F in fields:
                carry,chunk=divmod(F+carry,q)
                assert carry in (0,1)
                chunks.append(chunk);carries.append(carry)
            assert carries[0]==carries[1]==carries[3]==0
            A=F0+F1-2*H;D=F2+F3-2*H
            if carries[2]:
                assert chunks[2]==chunks[3]==H and D==q-1
                boundary+=1
            else:
                assert all(prior.base.prior.native(F,t) for F in fields)
                native+=1
            for m in range(1,t+1):
                W=3**m;I=D-W*A
                if not (0<I<W and I%6==0 and P%2==0):continue
                assert not carries[2]
                assert all(0<F<q for F in fields)
                planes=[tuple((F-H)//3**j%3 for j in range(t)) for F in fields]
                reads=[planes[2][j]+planes[3][j] for j in range(t)]
                appends=[planes[0][j]+planes[1][j] for j in range(t)]
                assert prior.direct_fifo(I,W,reads,appends) and planes[0][0]==1
                full_fifo+=1
        assert boundary>0 if t>=2 else boundary==0
        rows.append(dict(t=t,bounded_positive_field_tuples=checked,
                         valuation_accepted=valuation_accepted,native=native,
                         exceptional_all_two_read_cases=boundary,
                         accepted_initial_6x_fifo_cases=full_fifo))
    return rows


def positive_outer(x,read_choice=0):
    I=6*x;W=9;m=2
    while W<=I:W*=3;m+=1
    q=3*W;t=m+1;H=(q-1)//2
    reads=[I//3**j%3 for j in range(m)]+[1]
    appends=[1]+[0]*m
    d0=[int(v==2 or (v==1 and read_choice==0)) for v in reads]
    d1=[v-bit for v,bit in zip(reads,d0)]
    fields=[H+1,H,H+prior.word(d0),H+prior.word(d1)]
    A,D=1,I+W;r=prior.base.prior.packed(fields,q)
    values=dict(x=x,W=W,q=q,r=r,alphaP=q**4-r,alphaA=q-A,alphaD=q-D,
                beta=W-I,L=q//W,**{f'F{i}':F for i,F in enumerate(fields)})
    assert min(values.values())>0 and r%2==0
    assert selector.valuation(r)==4*t and prior.direct_fifo(I,W,reads,appends)
    env=selector.execute(PREFIX+FIFO+BOUNDS,values)
    for left,right in [('r','packed'),('packed_bound','n2'),('append_bound','q'),('read_bound','q'),
                       ('read_sum','transport'),('width_bound','W'),('q','length_product')]:
        assert env[left]==env[right]
    return values


def converse():
    for x in range(1,201):
        for choice in (0,1):positive_outer(x,choice)
    return dict(ordinary_positive_inputs=200,positive_outer_maps=400,
                smallest_example=positive_outer(1),
                kernel_scope='Every positive retained Pell coordinate is supplied by the parametric four-field converse, not numerically materialized')


def old_boundary():
    q,W,H=27,9,13;fields=(14,14,40,12)
    P=prior.base.prior.packed(fields,q);A=fields[0]+fields[1]-2*H;D=fields[2]+fields[3]-2*H
    I=D-W*A
    assert 0<P<q**4 and P%2==0 and selector.valuation(P)==12
    assert A<q and D<q and I==W-1==8
    assert fields[2]>=q and I%6!=0
    return dict(q=q,W=W,fields=list(fields),P=P,A=A,D=D,old_initial=I,
                scope='Survives the three aggregate bounds with old I=2x, but fails new I=6x')


def controller_extension():
    source=source_check()
    carry=prior.conditional_carry_schedule(True,False,True)
    constants=['weight0','weight1','weight2','weight3','lambda','minus_lambda','cs','cf','cs_actual']
    inputs={name:sp.Symbol(name) for name in source['positive_parameters']+source['positive_auxiliaries']+constants}
    weighted=sum(inputs[f'weight{i}']*inputs[f'F{i}'] for i in range(4))
    expected=weighted+inputs['lambda']*(inputs['q']-1)
    schedules={
        'literal10':carry['instructions'],
        'general9':carry['instructions'][:-1],
        'equal_endpoints8':carry['instructions'][:7]+[['carry_negative_offset','*','minus_lambda','twice_H']],
    }
    results={}
    for name,schedule in schedules.items():
        combined=source['instructions']+schedule
        env=selector.execute(combined,inputs)
        if name=='literal10':
            residual=env['controller']
            target=expected+inputs['cs']
            equality=['controller',0]
        elif name=='general9':
            residual=env['carry_with_offset']-(inputs['cf']-inputs['cs_actual'])
            target=expected+inputs['cs_actual']-inputs['cf']
            equality=['carry_with_offset','fixed numeral cf-cs_actual']
        else:
            residual=(env['carry_s0123']-env['carry_negative_offset']).subs(inputs['minus_lambda'],-inputs['lambda'])
            target=expected
            equality=['carry_s0123','carry_negative_offset']
        assert sp.expand(residual-target)==0,name
        counts=Counter(row[1] for row in combined)
        extra=len(schedule)
        assert extra=={'literal10':10,'general9':9,'equal_endpoints8':8}[name]
        assert counts['*']==38 and counts['+']+counts['-']==26+extra
        results[name]=dict(operations=64+extra,multiplications=38,additions_subtractions=26+extra,
                           equations=18,extra_operations=extra,controller_instructions=schedule,
                           equality=equality)
    results.update(fixed_offset=carry['fixed_offset'],normalization=carry['normalization'],
                   equal_endpoint_scope='cs_actual=cf; their common value remains arbitrary and fixed',
                   scope='Exact conditional filtered carry architectures; no universal controller or loader is supplied')
    return results


def serialized_controller_extension():
    source=source_check()
    schedule=[('serialized_app_twice','+','append_fields','F0'),
              ('serialized_app_weight','*',8,'serialized_app_twice'),
              ('serialized_read0','*',176,'F2'),('serialized_read1','*',80,'F3'),
              ('serialized_read_total','+','serialized_read0','serialized_read1'),
              ('serialized_offset','*',143,'twice_H'),
              ('serialized_left','+','serialized_app_weight','serialized_offset')]
    inputs={name:sp.Symbol(name) for name in source['positive_parameters']+source['positive_auxiliaries']}
    combined=source['instructions']+schedule
    env=selector.execute(combined,inputs)
    residual=env['serialized_left']-env['serialized_read_total']
    expected=16*inputs['F0']+8*inputs['F1']-176*inputs['F2']-80*inputs['F3']+143*(inputs['q']-1)
    assert sp.expand(residual-expected)==0
    H=sp.Symbol('H');planes=sp.symbols('A0 A1 D0 D1')
    decoded=residual.subs({inputs[f'F{i}']:H+plane for i,plane in enumerate(planes)}).subs(inputs['q'],2*H+1)
    assert sp.expand(decoded-(16*planes[0]+8*planes[1]-176*planes[2]-80*planes[3]+54*H))==0
    counts=Counter(row[1] for row in combined)
    assert len(combined)==71 and counts['*']==37 and counts['+']+counts['-']==34
    return dict(operations=71,multiplications=37,additions_subtractions=34,equations=18,
                extra_operations=7,controller_instructions=[list(row) for row in schedule],
                equality=['serialized_left','serialized_read_total'],
                original_coefficients=dict(append=[8,4],read=[-88,-40],h=27,start=0,finish=0),
                scaled_coefficients=dict(append=[16,8],read=[-176,-80],h=54,start=0,finish=0),
                scope='Exact whole unfiltered carry graph of the small serialized candidate; its block code, loader and cleanup are not enforced')


def verify():
    return dict(status='PASS_COMPLETE_DUALRAIL_FIFO_64',source=source_check(),
                field_carries=field_carry_scan(),all_inputs=converse(),old_boundary=old_boundary(),
                carry_extensions=controller_extension(),serialized_carry71=serialized_controller_extension(),
                dependencies={Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (prior,prior.base,prior.base.prior,selector)},
                scope='Exact raw FIFO with initial6x and a positive first append rail; controller universality remains open',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','dependencies')},indent=2))
