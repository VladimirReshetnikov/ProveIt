"""Exact66 cyclic NAND relation and bounded native-state compiler search."""
import argparse
from itertools import product,permutations
from pathlib import Path
from collections import Counter
import hashlib
import json
import sympy as sp
import native_controller_three_selector_53 as selector

EXTRA = [('Dword','-','twice_H','F2'),('S1','+','Hrep','F2'),('Sword','-','S1','F0'),
         ('ports','+','portA','portB'),
         ('RA0','*','R0','portA'),('guard0','*','twice_H','K0'),('rhs0','+','Dword','guard0'),('div0','*','R0','Z0'),
         ('RA1','*','R1','portB'),('guard1','*','twice_H','K1'),('rhs1','+','Dword','guard1'),('div1','*','R1','Z1')]


def source_check():
    names = ['q','F0','F1','F2','Hrep']+selector.CORE_NAMES+['R0','R1','portA','portB','K0','K1','Z0','Z1']
    z = {n:sp.Symbol(n) for n in names}
    schedule = selector.OUTER54+selector.CORE+EXTRA
    env = selector.execute(schedule,z)
    equalities = [('q','q_calc'),('sum012','four_H'),('r','packed')]+selector.kernel.EQUALITIES[1:]
    equalities += [('ports','Sword'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]
    polynomials = selector.sources(z,True)
    H,F0,F2,q = (z[n] for n in ('Hrep','F0','F2','q'))
    polynomials += [z['portA']+z['portB']-H-F2+F0,
                    z['R0']*z['portA']-(2*H-F2)-2*H*z['K0'],q-z['R0']*z['Z0'],
                    z['R1']*z['portB']-(2*H-F2)-2*H*z['K1'],q-z['R1']*z['Z1']]
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[10]*(u*u-z['y_aux']**2)
    records = []
    for ix,((left,right),source) in enumerate(zip(equalities,polynomials)):
        adjust = correction if ix == 11 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    count = Counter(row[1] for row in schedule)
    assert len(schedule)==66 and count['*']==35 and count['+']+count['-']==31
    assert len(equalities)==len(polynomials)==18
    return dict(operations=66,multiplications=35,additions_subtractions=31,equations=18,
                parameters=['q','F0','F1','F2','R0','R1'],auxiliaries=['Hrep']+selector.CORE_NAMES+['portA','portB','K0','K1','Z0','Z1'],
                instructions=[list(row) for row in schedule],sources=records)


PROJECTIONS = [(1,0,0),(1,0,1),(1,1,0)]


def rule_extra(alpha,beta,perm):
    extra=[]
    for name,bits in zip(('W0','W1'),(alpha,beta)):
        assert bits in PROJECTIONS
        if bits==(1,0,0):
            extra.append((name,'-','F0','Hrep'))
        else:
            extra.append((name,'-','twice_H',f'F{bits.index(0)}'))
    extra += [('S1','+','Hrep',f'F{perm[2]}'),('Sword','-','S1',f'F{perm[0]}'),
              ('ports','+','portA','portB')]
    for i,port in enumerate(('portA','portB')):
        extra += [(f'RA{i}','*',f'R{i}',port),(f'guard{i}','*','twice_H',f'K{i}'),
                  (f'rhs{i}','+',f'W{i}',f'guard{i}'),(f'div{i}','*',f'R{i}',f'Z{i}')]
    return extra


def rule_source_check():
    names=['q','F0','F1','F2','Hrep']+selector.CORE_NAMES+['R0','R1','portA','portB','K0','K1','Z0','Z1']
    z={n:sp.Symbol(n) for n in names};H=z['Hrep'];F=[z[f'F{i}'] for i in range(3)]
    equalities=[('q','q_calc'),('sum012','four_H'),('r','packed')]+selector.kernel.EQUALITIES[1:]
    equalities += [('ports','Sword'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]
    base=selector.sources(z,True);u=2*z['r']+1+z['j']*z['c']
    correction=base[10]*(u*u-z['y_aux']**2)
    records=[]
    for alpha,beta,perm in product(PROJECTIONS,PROJECTIONS,permutations(range(3))):
        extra=rule_extra(alpha,beta,perm);schedule=selector.OUTER54+selector.CORE+extra
        env=selector.execute(schedule,z)
        words=[sum(bits[i]*(F[i]-H) for i in range(3)) for bits in (alpha,beta)]
        # Complement expressions agree modulo the already-paid selector checksum.
        checksum=sum(F)-4*H
        direct=[z['portA']+z['portB']-H-F[perm[2]]+F[perm[0]]]
        for i,port in enumerate(('portA','portB')):
            direct += [z[f'R{i}']*z[port]-words[i]-2*H*z[f'K{i}'],z['q']-z[f'R{i}']*z[f'Z{i}']]
        polynomials=base+direct
        adjustments={11:correction}
        for i,bits in enumerate((alpha,beta)):
            if sum(bits)==2:adjustments[14+2*i]=checksum
        for ix,((left,right),source) in enumerate(zip(equalities,polynomials)):
            assert sp.expand(env[left]-env[right]-source-adjustments.get(ix,0))==0,(alpha,beta,perm,ix)
        counts=Counter(row[1] for row in schedule)
        assert len(schedule)==67 and counts['*']==35 and counts['+']+counts['-']==32
        assert len(equalities)==len(polynomials)==18
        records.append(dict(alpha=list(alpha),beta=list(beta),permutation=list(perm),
                            extra_instructions=[list(row) for row in extra],
                            additional_sources=[str(sp.expand(p)) for p in direct],
                            residual_adjustments={str(k):str(sp.expand(v)) for k,v in adjustments.items() if k!=11}))
    return dict(operations=67,multiplications=35,additions_subtractions=32,equations=18,variants=records)


def ternary_word(bits):
    return sum(v*3**j for j,v in enumerate(bits))


def right_rotate(value,t,amount):
    q,R=3**t,3**amount
    return value//R+(q//R)*(value%R)


def cyclic_candidates():
    tuples = admitted = 0
    positive_witness_examples = []
    for t in range(1,6):
        q=3**t;H=(q-1)//2
        for tail in product(range(3),repeat=t-1):
            labels=(0,)+tail
            T=[sum(3**j for j,x in enumerate(labels) if x==i) for i in range(3)]
            fields=[H+x for x in T]
            D=H-T[2];S=H-T[0]+T[2]
            assert D>0 and D%3==1 and 0<=S<=q-1
            for a,b in product(range(1,t+1),repeat=2):
                R0,R1=3**a,3**b
                realA,realB=right_rotate(D,t,a),right_rotate(D,t,b)
                for A in range(1,S):
                    B=S-A
                    n0,n1=R0*A-D,R1*B-D
                    arithmetic=n0>0 and n1>0 and n0%(q-1)==0 and n1%(q-1)==0
                    semantic=A==realA and B==realB
                    assert arithmetic==semantic
                    if arithmetic:
                        assert all((D//3**j%3)==1-(A//3**j%3)*(B//3**j%3) for j in range(t))
                        K0,K1=n0//(q-1),n1//(q-1)
                        assert K0==D%R0 and K1==D%R1 and K0>0 and K1>0
                        if len(positive_witness_examples)<3:
                            positive_witness_examples.append(dict(t=t,q=q,fields=fields,R0=R0,R1=R1,A=A,B=B,K0=K0,K1=K1,Z0=q//R0,Z1=q//R1))
                        admitted+=1
                    tuples+=1
    assert admitted>0
    return dict(arbitrary_positive_port_tuples=tuples,admitted=admitted,examples=positive_witness_examples)


def rotate_bits(x,t,a):
    a%=t;mask=(1<<t)-1
    return ((x>>a)|(x<<(t-a)))&mask


def rule_candidates():
    candidates=admitted=0
    for t in range(1,5):
        q=3**t;H=(q-1)//2
        for tail in product(range(3),repeat=t-1):
            labels=(0,)+tail
            for alpha,beta,perm in product(PROJECTIONS,PROJECTIONS,permutations(range(3))):
                inverse=[perm.index(i) for i in range(3)]
                W0=ternary_word([alpha[x] for x in labels]);W1=ternary_word([beta[x] for x in labels])
                S=ternary_word([inverse[x] for x in labels])
                assert W0%3==W1%3==1 and 0<W0<=H and 0<W1<=H
                for a,b in product(range(t+1),repeat=2):
                    R0,R1=3**a,3**b
                    actualA,actualB=right_rotate(W0,t,a),right_rotate(W1,t,b)
                    for A in range(1,S):
                        B=S-A;n0=R0*A-W0;n1=R1*B-W1
                        arithmetic=n0>0 and n1>0 and n0%(q-1)==0 and n1%(q-1)==0
                        semantic=a>0 and b>0 and A==actualA and B==actualB
                        assert arithmetic==semantic,(t,alpha,beta,perm,a,b,A,B)
                        if arithmetic:
                            assert all(labels[j]==perm[alpha[labels[(j+a)%t]]+beta[labels[(j+b)%t]]] for j in range(t))
                            admitted+=1
                        candidates+=1
    assert admitted>0
    return dict(arbitrary_positive_port_tuples=candidates,admitted=admitted,maximum_t=4)


def commuting_nand():
    candidates=accepted=0
    for t in range(1,13):
        mask=(1<<t)-1
        for a,b in product(range(t),repeat=2):
            for D in range(1<<t):
                candidates+=1
                A,B=rotate_bits(D,t,a),rotate_bits(D,t,b)
                if D != mask^(A&B):
                    continue
                assert D==rotate_bits(D,t,a+b)
                assert D==rotate_bits(D,t,a+b)&(rotate_bits(D,t,2*a)|rotate_bits(D,t,2*b))
                accepted+=1
    return dict(candidates=candidates,solutions=accepted,max_cycle_length=12)


def ca_tables():
    return sorted({tuple(perm[alpha[x]+beta[y]] for x,y in product(range(3),repeat=2))
                   for alpha,beta,perm in product(product((0,1),repeat=3),product((0,1),repeat=3),permutations(range(3)))})


def evolve(row,table,steps):
    for _ in range(steps):
        row=tuple(table[3*a+b] for a,b in zip(row,row[1:]))
    return row


def embedding_search():
    tables=ca_tables();assert len(tables)==147
    rows=[]
    mixed=((0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,0,1),(1,1,0))
    for m in range(1,7):
        tested=candidates=matches=0
        for table in tables:
            for c1 in product(range(3),repeat=m):
                # Rule110(111)=0 forces c0; this exhausts every pair of codes.
                tested+=1
                c0=evolve(c1*3,table,2*m)
                if c0==c1 or evolve(c0*3,table,2*m)!=c0:
                    continue
                candidates+=1;enc=(c0,c1)
                if all(evolve(sum((enc[x] for x in bits),()),table,2*m)==enc[(110>>(4*bits[0]+2*bits[1]+bits[2]))&1] for bits in mixed):
                    matches+=1
        assert matches==0
        rows.append(dict(block_width=m,time_scale=2*m,forced_code_pairs=tested,quiescent_candidates=candidates,matches=matches))
    return dict(distinct_tables=len(tables),domains=rows,scope='Only direct binary block codes with time_scale=2*block_width; no general universality claim')


def verify():
    return dict(scope='Complete66 cyclic NAND component; no complete universal bound improvement',source=source_check(),
                rule_sources=rule_source_check(),
                cyclic=cyclic_candidates(),rule_candidates=rule_candidates(),commuting=commuting_nand(),embedding=embedding_search(),
                dependency_sha256=hashlib.sha256(Path(selector.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest())


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','rule_sources')},indent=2))
