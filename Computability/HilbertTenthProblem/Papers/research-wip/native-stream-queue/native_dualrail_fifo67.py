"""Exact67 native dual-rail FIFO with ordinary input6x+2; controller unpaid."""
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_controller_four_fields55 as base

selector=base.selector
EXTRA=[('read_fields','+','F0','F1'),('read_sum','-','read_fields','twice_H'),
       ('append_fields','+','F2','F3'),('append_sum','-','append_fields','twice_H'),
       ('six_x','*',6,'x'),('initial','+','six_x',2),
       ('scaled_append','*','W','append_sum'),('transport','+','initial','scaled_append'),
       ('width_bound','+','initial','beta'),('length_product','*','W','L')]


def source_check():
    parameters=['x','W','q','F0','F1','F2','F3']
    auxiliaries=selector.CORE_NAMES+[f'alpha{i}' for i in range(4)]+['Hrep','beta','L']
    z={name:sp.Symbol(name) for name in parameters+auxiliaries}
    outer=[row for row in base.prior.OUTER if row[0]!='even_r']
    schedule=outer+base.prior.EXPOSE_H+selector.CORE+EXTRA
    env=selector.execute(schedule,z)
    equalities=[(f'bound{i}','q') for i in range(4)]+[('r','packed'),('q','q_calc')]
    equalities+=selector.kernel.EQUALITIES[1:]
    equalities+=[('read_sum','transport'),('width_bound','W'),('q','length_product')]
    old=base.prior.independent_sources(dict(z,nu=sp.Symbol('unused_nu')),True)
    sources=old[:5]+old[6:]
    norm_index=len(sources)-3
    read=z['F0']+z['F1']-2*z['Hrep'];append=z['F2']+z['F3']-2*z['Hrep']
    initial=6*z['x']+2
    sources += [read-initial-z['W']*append,initial+z['beta']-z['W'],z['q']-z['W']*z['L']]
    u=2*z['r']+1+z['j']*z['c'];correction=sources[norm_index]*(u*u-z['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if ix==norm_index+1 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==67 and counts['*']==33 and counts['+']+counts['-']==34
    assert len(equalities)==len(sources)==19 and len(auxiliaries)==24
    assert len(set(parameters+auxiliaries))==len(parameters+auxiliaries)
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=67,multiplications=33,additions_subtractions=34,equations=19,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def word(bits):
    return sum(bit*3**j for j,bit in enumerate(bits))


def direct_fifo(initial,width,reads,appends):
    queue=initial
    for read,append in zip(reads,appends):
        if queue%3!=read:return False
        queue=queue//3+(width//3)*append
        assert 0<=queue<width
    return queue==0


def exhaustive():
    checked=accepted=zero_append=0
    for t in range(2,5):
        q=3**t;H=(q-1)//2
        for m in range(2,t+1):
            W=3**m
            for x in range(1,(W-3)//6+1):
                initial=6*x+2
                assert initial<W
                for tail in product((0,1),repeat=4*t-1):
                    bits=(1,)+tail
                    planes=[bits[i*t:(i+1)*t] for i in range(4)]
                    streams=[word(plane) for plane in planes]
                    fields=[H+value for value in streams]
                    reads=[planes[0][j]+planes[1][j] for j in range(t)]
                    appends=[planes[2][j]+planes[3][j] for j in range(t)]
                    arithmetic=(sum(fields)%2==0 and streams[0]+streams[1]==initial+W*(streams[2]+streams[3]))
                    semantic=direct_fifo(initial,W,reads,appends)
                    assert arithmetic==semantic,(x,t,m,planes)
                    checked+=1
                    if arithmetic:
                        accepted+=1;zero_append+=streams[2]+streams[3]==0
                        values=dict(x=x,W=W,q=q,Hrep=H,beta=W-initial,L=q//W,
                                    **{f'F{i}':value for i,value in enumerate(fields)})
                        env=selector.execute(base.prior.EXPOSE_H+EXTRA,values)
                        assert env['read_sum']==env['transport'] and env['width_bound']==W
                        assert env['length_product']==q and min(values.values())>0
                        r=base.prior.packed(fields,q)
                        assert r%2==0 and selector.valuation(r)==4*t
    assert accepted>0 and zero_append>0
    return dict(arbitrary_boolean_stream_tuples=checked,accepted=accepted,
                admitted_zero_append_sum=zero_append,maximum_t=4)


def all_input_converse():
    checked=0
    for x in range(1,201):
        initial=6*x+2;W=9;m=2
        while W<=initial:W*=3;m+=1
        q=W;H=(q-1)//2
        # Read the initial queue and append zero for one complete pass.
        trits=[initial//3**j%3 for j in range(m)]
        for assignment in (0,1):
            d0=[int(v==2 or (v==1 and assignment==0)) for v in trits]
            d1=[v-bit for v,bit in zip(trits,d0)]
            fields=[H+word(d0),H+word(d1),H,H]
            assert d0[0]==d1[0]==1 and sum(fields)%2==0
            assert direct_fifo(initial,W,trits,[0]*m)
            r=base.prior.packed(fields,q)
            assert selector.valuation(r)==4*m
            checked+=1
    return dict(ordinary_positive_inputs=200,positive_outer_maps=checked,
                meaning='The bare FIFO component admits every input; a controller is essential.')


def conditional_carry_schedule():
    z=sp.symbols('F0 F1 F2 F3 H weight0 weight1 weight2 weight3 cs')
    F=z[:4];H=z[4];coeff=z[5:9];cs=z[9]
    decoded=sum(c*(f-H) for c,f in zip(coeff,F))+cs
    paid=sum(c*f for c,f in zip(coeff,F))+cs
    assert sp.expand(paid-decoded-H*sum(coeff))==0
    schedule=[(f'carry_p{i}','*',f'weight{i}',f'F{i}') for i in range(4)]+[
        ('carry_s01','+','carry_p0','carry_p1'),('carry_s012','+','carry_s01','carry_p2'),
        ('carry_s0123','+','carry_s012','carry_p3'),('controller','+','carry_s0123','cs')]
    env=selector.execute(schedule,{str(symbol):symbol for symbol in z})
    assert sp.expand(env['controller']-paid)==0
    assert len(schedule)==8 and Counter(row[1] for row in schedule)=={'*':4,'+':4}
    source=source_check()
    full_inputs={name:sp.Symbol(name) for name in source['positive_parameters']+source['positive_auxiliaries']}
    full_inputs.update({str(symbol):symbol for symbol in coeff+(cs,)})
    combined=source['instructions']+schedule
    assert len(combined)==75
    full_env=selector.execute(combined,full_inputs)
    assert sp.expand(full_env['controller']-paid)==0
    return dict(extra_operations=8,multiplications=4,additions_subtractions=4,
                candidate_total=75,fixed_constraint='c0+c1+c2+c3=0',
                instructions=[list(row) for row in schedule],
                source='c0*F0+c1*F1+c2*F2+c3*F3+cs=0',
                local_relation='3 carry_next=carry+c0*d0+c1*d1+c2*a0+c3*a1',
                scope='Exact conditional affine carry relation only; no universal compiler for these fixed coefficients is known.')


def verify():
    return dict(status='PASS_COMPLETE_DUALRAIL_FIFO_67',source=source_check(),
                exhaustive=exhaustive(),all_inputs=all_input_converse(),
                conditional_carry=conditional_carry_schedule(),
                dependencies={Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (base,base.prior,selector)},
                established_complete_universal_bound=76,
                scope='Exact bounded FIFO initialized by6x+2; no universal synchronized controller or accepting computation.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','dependencies')},indent=2))
