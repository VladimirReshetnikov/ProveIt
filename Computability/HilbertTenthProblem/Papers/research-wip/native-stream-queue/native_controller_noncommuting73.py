"""Complete73 finite NAND relation with paid noncommuting routing."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_three_selector_53 as selector

EXTRA = [
    ('Dword','-','twice_H','F2'),('S1','+','Hrep','F2'),('Sword','-','S1','F0'),
    ('portA','+','C','Q'),('ports','+','portA','portB'),
    ('E3','*',3,'E'),('Eword','+','E3',1),('q_from_Q','*',3,'Q'),
    ('tail_modulus','-','Q',1),('RA0','*','R0','C'),('lhs0','+','RA0','tail_modulus'),
    ('guard0','*','tail_modulus','K0'),('rhs0','+','E','guard0'),
    ('div0','*','R0','Z0'),('boundQ','+','C','Jbound'),
    ('RA1','*','R1','portB'),('guard1','*','twice_H','K1'),
    ('rhs1','+','Dword','guard1'),('div1','*','R1','Z1')]


def source_check():
    auxiliaries=['Hrep']+selector.CORE_NAMES+['C','E','Q','Jbound','portB','K0','K1','Z0','Z1']
    parameters=['q','F0','F1','F2','R0','R1']
    z={n:sp.Symbol(n) for n in parameters+auxiliaries}
    schedule=selector.OUTER54+selector.CORE+EXTRA
    env=selector.execute(schedule,z)
    equalities=[('q','q_calc'),('sum012','four_H'),('r','packed')]+selector.kernel.EQUALITIES[1:]
    equalities += [('Eword','Dword'),('q','q_from_Q'),('Q','div0'),('boundQ','Q'),
                   ('lhs0','rhs0'),('ports','Sword'),('RA1','rhs1'),('q','div1')]
    H,F0,F2,q,Q,C,E=(z[n] for n in ('Hrep','F0','F2','q','Q','C','E'))
    sources=selector.sources(z,True)
    sources += [3*E+1-2*H+F2,q-3*Q,Q-z['R0']*z['Z0'],C+z['Jbound']-Q,
                z['R0']*C+(Q-1)-E-(Q-1)*z['K0'],C+Q+z['portB']-H-F2+F0,
                z['R1']*z['portB']-2*H+F2-2*H*z['K1'],q-z['R1']*z['Z1']]
    u=2*z['r']+1+z['j']*z['c'];correction=sources[10]*(u*u-z['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if ix==11 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==73 and counts['*']==37 and counts['+']+counts['-']==36
    assert len(equalities)==len(sources)==21 and len(auxiliaries)==27
    return dict(operations=73,multiplications=37,additions_subtractions=36,equations=21,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def word(digits):
    return sum(d*3**j for j,d in enumerate(digits))


def rotate(value,t,amount):
    R=3**amount;q=3**t
    return value//R+(q//R)*(value%R)


def integer_candidates():
    checked=admitted=0;examples=[]
    for t in range(2,7):
        q=3**t;Q=q//3;H=(q-1)//2
        for tail in product(range(3),repeat=t-1):
            labels=(0,)+tail
            T=[sum(3**j for j,x in enumerate(labels) if x==i) for i in range(3)]
            D=H-T[2];S=H-T[0]+T[2]
            if D==1:continue
            E=(D-1)//3
            assert 0<E< Q and 3*E+1==D
            for a,b in product(range(t),range(1,t+1)):
                R0,R1=3**a,3**b;actualC=rotate(E,t-1,a);actualB=rotate(D,t,b)
                for C in range(1,Q):
                    B=S-C-Q
                    if B<=0:continue
                    n0=R0*C-E;n1=R1*B-D
                    arithmetic=n0%(Q-1)==0 and 1+n0//(Q-1)>0 and n1>0 and n1%(q-1)==0
                    semantic=C==actualC and B==actualB
                    assert arithmetic==semantic,(t,labels,a,b,C,B)
                    if arithmetic:
                        A=C+Q
                        assert all(D//3**j%3==1-(A//3**j%3)*(B//3**j%3) for j in range(t))
                        assert A%3==B%3==0 and 1+n0//(Q-1)==1+E%R0
                        admitted+=1
                        if len(examples)<3:examples.append(dict(t=t,labels=list(labels),R0=R0,R1=R1,D=D,E=E,C=C,A=A,B=B))
                    checked+=1
    assert admitted>0
    return dict(arbitrary_positive_port_tuples=checked,admitted=admitted,maximum_t=6,examples=examples)


def noncommuting_example():
    d=(1,0,0,1,1);a,b=1,2;t=len(d)
    P=lambda x:x[1+a:]+x[1:1+a]+x[:1]
    Q=lambda x:x[b:]+x[:b]
    A=P(d);B=Q(d)
    assert d==tuple(1-x*y for x,y in zip(A,B)) and A[0]==B[0]==0
    assert P(Q(d))!=Q(P(d)) and d!=P(Q(d))
    values=dict(q=243,Hrep=121,F0=122,F1=229,F2=133,R0=3,R1=9,
                Dword=109,Q=81,E=36,C=12,Jbound=69,portA=93,portB=39,K0=1,K1=1,Z0=27,Z1=27)
    assert word(d)==values['Dword'] and word(A)==values['portA'] and word(B)==values['portB']
    return dict(values=values,D=list(d),A=list(A),B=list(B),PQD=list(P(Q(d))),QPD=list(Q(P(d))))


def missing_bound_counterexample():
    q,Q,H=243,81,121;F0,F1,F2=122,133,229
    D,S,E,C,A,B,R0,R1,K0,K1,Z0,Z1=13,228,4,108,189,39,3,81,5,13,27,3
    assert F0+F1+F2==4*H and D==2*H-F2 and S==H+F2-F0
    assert D==3*E+1 and q==3*Q and Q==R0*Z0
    assert R0*C+(Q-1)==E+(Q-1)*K0 and A==C+Q and A+B==S
    assert R1*B==D+(q-1)*K1 and q==R1*Z1
    assert C>=Q and any(A//3**j%3==2 for j in range(5))
    return dict(q=q,Q=Q,H=H,fields=[F0,F1,F2],D=D,S=S,E=E,C=C,A=A,B=B,
                R0=R0,R1=R1,K0=K0,K1=K1,Z0=Z0,Z1=Z1,
                conclusion='Without the paid C+Jbound=Q comparison, this72-operation weakened relation admits a non-Boolean port.')


def verify():
    return dict(scope='Complete73 finite noncommuting NAND component; no universal certificate claim',
                source=source_check(),finite=integer_candidates(),noncommuting_example=noncommuting_example(),
                missing_bound_counterexample=missing_bound_counterexample(),
                dependency_sha256=hashlib.sha256(Path(selector.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest())


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k!='source'},indent=2))
