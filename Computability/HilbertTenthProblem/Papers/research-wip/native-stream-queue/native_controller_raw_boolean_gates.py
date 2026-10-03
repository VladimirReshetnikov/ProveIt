"""Raw Boolean ternary fields55, selectors53 and exact finite NAND64/71."""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path

import sympy as sp
import input_bridge_boolean_ternary60 as raw

prior = raw.prior


def packing(n):
    rows = []
    value = f'F{n-1}'
    for j in reversed(range(n-1)):
        rows += [(f'rb_mul{j}', '*', 'q', value),
                 (f'rb_sum{j}', '+', f'F{j}', f'rb_mul{j}')]
        value = f'rb_sum{j}'
    return rows


SELECTOR = [('Dword', '+', 'F0', 'F1'), ('rb_total', '+', 'Dword', 'F2'),
            ('twice_H', '+', 'Hrep', 'Hrep'), ('rb_q', '+', 'twice_H', 1)]
NAND = [('rb_twice_F2', '+', 'F2', 'F2'), ('Sword', '+', 'F1', 'rb_twice_F2'),
        ('ports', '+', 'portA', 'portB')]
ROTATIONS = []
for i in (0, 1):
    ROTATIONS += [(f'RA{i}', '*', f'R{i}', ('portA', 'portB')[i]),
                  (f'guard{i}', '*', 'twice_H', f'K{i}'),
                  (f'rhs{i}', '+', 'Dword', f'guard{i}'),
                  (f'div{i}', '*', f'R{i}', f'Z{i}')]
TAIL = [('rb_twice_F2', '+', 'F2', 'F2'), ('Sword', '+', 'F1', 'rb_twice_F2'),
        ('portA', '+', 'C', 'Q'), ('ports', '+', 'portA', 'portB'),
        ('E3', '*', 3, 'E'), ('Eword', '+', 'E3', 1), ('q_from_Q', '*', 3, 'Q'),
        ('tail_modulus', '-', 'Q', 1), ('RA0', '*', 'R0', 'C'),
        ('lhs0', '+', 'RA0', 'tail_modulus'),
        ('guard0', '*', 'tail_modulus', 'K0'), ('rhs0', '+', 'E', 'guard0'),
        ('div0', '*', 'R0', 'Z0'), ('boundQ', '+', 'C', 'Jbound'),
        ('RA1', '*', 'R1', 'portB'), ('guard1', '*', 'twice_H', 'K1'),
        ('rhs1', '+', 'Dword', 'guard1'), ('div1', '*', 'R1', 'Z1')]


def source_check(variant):
    selectors = variant != 'fields55'
    n = 3 if selectors else 4
    parameters = ['q']+[f'F{i}' for i in range(n)]
    auxiliaries = prior.CORE_NAMES+['bound_beta']
    if selectors:
        auxiliaries += ['Hrep']
    else:
        auxiliaries += [f'alpha{i}' for i in range(4)]
    if variant == 'nand64':
        parameters += ['R0', 'R1']
        auxiliaries += ['portA', 'portB', 'K0', 'K1', 'Z0', 'Z1']
    if variant == 'route71':
        parameters += ['R0', 'R1']
        auxiliaries += ['C', 'E', 'Q', 'Jbound', 'portB', 'K0', 'K1', 'Z0', 'Z1']
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries}
    schedule = packing(n)+raw.CORE+[('rb_X_bound', '+', 'r', 'bound_beta')]
    equalities = [('r', 'rb_sum0')]+prior.kernel.EQUALITIES[1:]+[('rb_X_bound', 'wn2')]
    # The ten independent changed-kernel polynomials do not depend on the fields.
    zz = dict(z, F3=z.get('F3', 0), alpha=0)
    polynomials = [z['r']-sum(z[f'F{i}']*z['q']**i for i in range(n))]
    polynomials += raw.independent_sources(zz, False)[1:11]
    polynomials += [z['r']+z['bound_beta']-z['w']*z['q']]
    if selectors:
        schedule += SELECTOR
        equalities += [('rb_total', 'Hrep'), ('rb_q', 'q')]
        polynomials += [sum(z[f'F{i}'] for i in range(3))-z['Hrep'], 2*z['Hrep']+1-z['q']]
    else:
        for i in range(4):
            schedule += [(f'rb_bound{i}', '+', f'F{i}', f'alpha{i}')]
            equalities += [(f'rb_bound{i}', 'q')]
            polynomials += [z[f'F{i}']+z[f'alpha{i}']-z['q']]
    D = z['F0']+z['F1']
    S = z['F1']+2*z['F2']
    if variant == 'nand64':
        schedule += NAND+ROTATIONS
        equalities += [('ports', 'Sword'), ('RA0', 'rhs0'), ('q', 'div0'),
                       ('RA1', 'rhs1'), ('q', 'div1')]
        polynomials += [z['portA']+z['portB']-S]
        for i, port in enumerate(('portA', 'portB')):
            polynomials += [z[f'R{i}']*z[port]-D-2*z['Hrep']*z[f'K{i}'],
                            z['q']-z[f'R{i}']*z[f'Z{i}']]
    if variant == 'route71':
        schedule += TAIL
        equalities += [('Eword', 'Dword'), ('q', 'q_from_Q'), ('Q', 'div0'), ('boundQ', 'Q'),
                       ('lhs0', 'rhs0'), ('ports', 'Sword'), ('RA1', 'rhs1'), ('q', 'div1')]
        q,Q,C,E = (z[k] for k in ('q', 'Q', 'C', 'E'))
        polynomials += [3*E+1-D, q-3*Q, Q-z['R0']*z['Z0'], C+z['Jbound']-Q,
                        z['R0']*C+Q-1-E-(Q-1)*z['K0'], C+Q+z['portB']-S,
                        z['R1']*z['portB']-D-2*z['Hrep']*z['K1'], q-z['R1']*z['Z1']]
    env = prior.execute(schedule, dict(z, n2=z['q']))
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[8]*(u*u-z['y_aux']**2)
    records = []
    assert len(equalities) == len(polynomials)
    for ix, ((left, right), p) in enumerate(zip(equalities, polynomials)):
        adjust = correction if ix == 9 else 0
        assert sp.expand(env[left]-env[right]-p-adjust) == 0, (variant, ix)
        records.append(dict(equality=[left,right], source=str(sp.expand(p)), correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    expected = {'fields55': (55,28,27,16,22), 'selectors53': (53,27,26,14,19),
                'nand64': (64,33,31,19,25), 'route71': (71,35,36,22,28)}[variant]
    assert (len(schedule),counts['*'],counts['+']+counts['-'],len(equalities),len(auxiliaries)) == expected
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    return dict(operations=len(schedule), multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(equalities),
                positive_parameters=parameters, positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule], sources=records)


def word(digits):
    return sum(d*3**j for j,d in enumerate(digits))


def rotate(value,t,amount):
    q,R = 3**t,3**amount
    return value//R+(q//R)*(value%R)


def prepower():
    cases = 0
    for q in range(2,19):
        for fields in product(range(1,q), repeat=4):
            r = raw.pack(fields,q)
            assert q**3+q*q+q+1 <= r < q**4 and r >= 15
            X=q*(r//q+1);Y=4;a=Y*(X+1);A=a+3;P=2*X*Y*Y+1
            assert X>r and a>2*r+1 and X*Y>r+1 and P>A and 6*X*Y*Y>a
            assert r+1>=16 and (2*A-1)**16>A*(A*A-1)**2
            cases += 1
    return dict(arbitrary_individually_bounded_field_tuples=cases, minimum_q=2, minimum_r=15)


def fields_check():
    rows=[]
    for t in (1,2,3):
        q=3**t;candidates=admitted=0
        for fields in product(range(1,q),repeat=4):
            r=raw.pack(fields,q)
            arithmetic=prior.valuation(r)==0 and r%2==0
            semantic=all(raw.native_boolean(f,t) for f in fields) and sum(fields)%2==0
            assert arithmetic==semantic
            candidates+=1;admitted+=arithmetic
        rows.append(dict(t=t,candidates=candidates,admitted=admitted))
    # No joint bound: four identical highest-bit words are admitted.
    q=9;fields=(3,3,3,3);r=raw.pack(fields,q)
    assert sum(fields)>=q and prior.valuation(r)==0 and r%2==0
    return dict(domains=rows, beyond_joint_bound=dict(q=q,fields=list(fields),r=r))


def selectors_check():
    rows=[]
    for t in range(1,7):
        q=3**t;H=(q-1)//2;candidates=admitted=0
        for f0 in range(1,H-1):
            for f1 in range(1,H-f0):
                fields=(f0,f1,H-f0-f1);r=raw.pack(fields,q)
                arithmetic=prior.valuation(r)==0 and r%2==0
                semantic=(t%2==0 and all(raw.native_boolean(f,t) for f in fields)
                          and all(sum(f//3**j%3 for f in fields)==1 for j in range(t)))
                assert arithmetic==semantic
                candidates+=1;admitted+=arithmetic
        assert admitted==(3**t-3*2**t+3 if t%2==0 else 0)
        rows.append(dict(t=t,candidates=candidates,admitted=admitted))
    return dict(domains=rows)


def nand_checks():
    checked=admitted=0;examples=[]
    for t in (4,6):
        q=3**t
        for labels in product(range(3),repeat=t):
            if len(set(labels))!=3:continue
            fields=[word([label==i for label in labels]) for i in range(3)]
            D=fields[0]+fields[1];S=fields[1]+2*fields[2]
            for a,b in product(range(t+1),repeat=2):
                RA,RB=3**a,3**b;trueA=rotate(D,t,a);trueB=rotate(D,t,b)
                # Every positive candidate A,B with their forced total is audited.
                for A in range(1,S):
                    B=S-A;n0=RA*A-D;n1=RB*B-D
                    arithmetic=n0>0 and n1>0 and n0%(q-1)==0 and n1%(q-1)==0
                    semantic=A==trueA and B==trueB and D%RA>0 and D%RB>0
                    assert arithmetic==semantic
                    if arithmetic:
                        assert all(D//3**j%3==1-(A//3**j%3)*(B//3**j%3) for j in range(t))
                        admitted+=1
                        if len(examples)<2:examples.append(dict(t=t,labels=list(labels),a=a,b=b,D=D,A=A,B=B))
                    checked+=1
    # The smallest audited lengths have no solution using all three labels.
    # A length-eight point demonstrates that the exact relation is nonempty.
    d=(1,0,0,0,1,1,1,1);t=8;a,b=3,5
    A=d[a:]+d[:a];B=d[b:]+d[:b];labels=tuple(x+y for x,y in zip(A,B))
    assert d==tuple(1-x*y for x,y in zip(A,B)) and set(labels)=={0,1,2}
    D=word(d);q=3**t;R0,R1=3**a,3**b
    assert R0*word(A)==D+(q-1)*(D%R0) and R1*word(B)==D+(q-1)*(D%R1)
    assert D%R0>0 and D%R1>0
    examples.append(dict(t=t,labels=list(labels),a=a,b=b,D=D,A=word(A),B=word(B)))
    return dict(arbitrary_positive_port_tuples=checked,admitted=admitted,examples=examples)


def route_checks():
    checked=admitted=0
    for t in (4,6):
        q=3**t;Q=q//3
        for labels in product(range(3),repeat=t):
            if len(set(labels))!=3:continue
            fields=[word([label==i for label in labels]) for i in range(3)]
            D=fields[0]+fields[1];S=fields[1]+2*fields[2]
            if D%3!=1:continue
            E=(D-1)//3
            assert E>0
            for a,b in product(range(t),range(t+1)):
                R0,R1=3**a,3**b;trueC=rotate(E,t-1,a);trueB=rotate(D,t,b)
                for C in range(1,Q):
                    B=S-C-Q
                    if B<=0:continue
                    n0=R0*C-E;n1=R1*B-D
                    arithmetic=n0%(Q-1)==0 and 1+n0//(Q-1)>0 and n1>0 and n1%(q-1)==0
                    semantic=C==trueC and B==trueB and D%R1>0
                    assert arithmetic==semantic
                    if arithmetic:
                        A=C+Q
                        assert all(D//3**j%3==1-(A//3**j%3)*(B//3**j%3) for j in range(t))
                        admitted+=1
                    checked+=1
    d=(1,0,0,0,1,1,1,1);t=8;a=b=3
    P=lambda z:z[1+a:]+z[1:1+a]+z[:1]
    Qrot=lambda z:z[b:]+z[:b]
    A=P(d);B=Qrot(d);labels=tuple(x+y for x,y in zip(A,B))
    assert d==tuple(1-x*y for x,y in zip(A,B)) and set(labels)=={0,1,2}
    assert P(Qrot(d))!=Qrot(P(d))
    q=3**t;Q=q//3;D=word(d);E=(D-1)//3;C=word(A[:-1]);fields=[word([l==i for l in labels]) for i in range(3)]
    values=dict(q=q,Hrep=(q-1)//2,F0=fields[0],F1=fields[1],F2=fields[2],R0=27,R1=27,
                Q=Q,E=E,C=C,Jbound=Q-C,portB=word(B),K0=1+E%27,K1=D%27,Z0=Q//27,Z1=q//27)
    env=prior.execute(SELECTOR+TAIL,values)
    for left,right in [('Eword','Dword'),('q','q_from_Q'),('Q','div0'),('boundQ','Q'),
                       ('lhs0','rhs0'),('ports','Sword'),('RA1','rhs1'),('q','div1')]:
        assert env[left]==env[right]
    assert all(v>0 for v in values.values())
    return dict(arbitrary_positive_port_tuples=checked,admitted=admitted,
                noncommuting_example=dict(values=values,d=list(d),labels=list(labels),A=list(A),B=list(B),
                                          PQ=list(P(Qrot(d))),QP=list(Qrot(P(d)))))


def verify():
    return dict(status='PASS_RAW_BOOLEAN_GATES', sources={v:source_check(v) for v in ('fields55','selectors53','nand64','route71')},
                prepower=prepower(),fields=fields_check(),selectors=selectors_check(),nand=nand_checks(),routing=route_checks(),
                scope='Exact typing and finite cyclic relations; ordinary input, circuit wiring and universal acceptance unpaid',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({k:result[k] for k in ('status','prepower','selectors','nand','routing')},indent=2))
