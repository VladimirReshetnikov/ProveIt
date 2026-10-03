"""Complete56 typing of two native Boolean streams and their complements."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_three_selector_53 as selector

OUTER = [
    ('twice_H','+','Hrep','Hrep'),('q_calc','+','twice_H',1),
    ('three_H','+','Hrep','twice_H'),('sum01','+','F0','F1'),('sum23','+','F2','F3'),
    ('p0','*','q','F3'),('p1','+','F2','p0'),('p2','*','q','p1'),
    ('p3','+','F1','p2'),('p4','*','q','p3'),('packed','+','F0','p4'),
    ('q2','*','q','q'),('n2','*','q2','q2')]


def independent_sources(z):
    q,H=z['q'],z['Hrep'];F=[z[f'F{i}'] for i in range(4)]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=(z[n] for n in selector.CORE_NAMES)
    X,Y=w*q**4,s*q**4;discriminant=a*a+6*a+8;u=2*r+1+j*c
    return [q-2*H-1,F[0]+F[1]-3*H,F[2]+F[3]-3*H,
            r-F[0]-q*F[1]-q*q*F[2]-q**3*F[3],
            ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(6*a+8),
            d*d-1-discriminant*c*c,(i*c*c)**2-discriminant*(f*f-1),
            discriminant*(f*f-1)*(u*u-ya*ya)-(1-ya*ya),u-c-o*f]


def source_check():
    parameters=['q','F0','F1','F2','F3'];auxiliaries=['Hrep']+selector.CORE_NAMES
    z={n:sp.Symbol(n) for n in parameters+auxiliaries}
    schedule=OUTER+selector.CORE;env=selector.execute(schedule,z)
    equalities=[('q','q_calc'),('sum01','three_H'),('sum23','three_H'),('r','packed')]
    equalities+=selector.kernel.EQUALITIES[1:]
    sources=independent_sources(z);u=2*z['r']+1+z['j']*z['c']
    correction=sources[11]*(u*u-z['y_aux']**2);records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if ix==12 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,ix
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==56 and counts['*']==30 and counts['+']+counts['-']==26
    assert len(equalities)==len(sources)==14 and len(auxiliaries)==18
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=56,multiplications=30,additions_subtractions=26,equations=14,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def packed(fields,q):
    return sum(F*q**i for i,F in enumerate(fields))


def native(F,t):
    return F<3**t and all(F//3**j%3 in (1,2) for j in range(t))


def prepower():
    checked=0
    for H in range(1,41):
        q=2*H+1;scale=q**4
        for F0,F2 in product(range(1,3*H),repeat=2):
            fields=(F0,3*H-F0,F2,3*H-F2);r=packed(fields,q)
            assert all(0<F<2*q for F in fields)
            assert r>=q**3+q*q+q+1>=40 and 2*r<3*scale
            assert scale>=81 and scale<r*r and scale*scale>r+1
            assert scale*(scale+1)>2*r+1 and scale*(scale+1)>12*r
            assert r%2==0
            checked+=1
    return dict(positive_pair_decompositions=checked,maximum_H=40,
                scope='No assumption that q is a power of3 or that any field is belowq')


def exhaustive_fields():
    records=[]
    for t in range(1,6):
        q=3**t;H=(q-1)//2;scale=q**4
        accepted=checked=packed_overflow=field_overflow=0
        for F0,F2 in product(range(1,3*H),repeat=2):
            fields=(F0,3*H-F0,F2,3*H-F2);P=packed(fields,q)
            valuation=selector.factorial_valuation(2*P)-2*selector.factorial_valuation(P)
            arithmetic=valuation>=4*t
            semantic=all(native(F,t) for F in fields) and F0%3==2
            assert arithmetic==semantic,(t,fields,P,valuation)
            if arithmetic:
                T=[F-H for F in fields]
                assert T[0]+T[1]==T[2]+T[3]==H
                assert all(T[0]//3**j%3+T[1]//3**j%3==1 and
                           T[2]//3**j%3+T[3]//3**j%3==1 for j in range(t))
                assert P%2==0 and valuation==4*t
                accepted+=1
            carry=0;chunk_sum=internal=0
            for i,F in enumerate(fields):
                carry,chunk=divmod(F+carry,q)
                assert carry in (0,1)
                chunk_sum+=chunk
                if i<3:internal+=carry
            assert chunk_sum==6*H-2*H*internal-q*carry
            checked+=1;packed_overflow+=P>=scale;field_overflow+=any(F>=q for F in fields)
        assert accepted==2**(2*t-1)
        records.append(dict(t=t,positive_field_tuples=checked,accepted=accepted,
                            packed_overflow=packed_overflow,field_overflow=field_overflow))
    return records


def canonical_pairs():
    checked=zero_decoded=0
    for t in range(1,7):
        q=3**t;H=(q-1)//2
        for tail in product((0,1),repeat=t-1):
            U=sum(bit*3**j for j,bit in enumerate((1,)+tail))
            for bits in product((0,1),repeat=t):
                V=sum(bit*3**j for j,bit in enumerate(bits))
                T=(U,H-U,V,H-V);fields=tuple(H+Ti for Ti in T)
                r=packed(fields,q)
                assert all(F>0 and native(F,t) for F in fields)
                assert fields[0]+fields[1]==fields[2]+fields[3]==3*H
                assert selector.factorial_valuation(2*r)-2*selector.factorial_valuation(r)==4*t
                assert r%2==0
                checked+=1;zero_decoded+=sum(Ti==0 for Ti in T)
    return dict(independent_boolean_word_pairs=checked,identically_zero_decoded_words=zero_decoded,maximum_t=6)


def verify():
    return dict(status='PASS_COMPLETE_NATIVE_BOOLEAN_PAIRS_56',source=source_check(),
                prepower=prepower(),field_scan=exhaustive_fields(),canonical=canonical_pairs(),
                actual_module_kernel_cases=[selector.kernel.check_canonical_ratio(r) for r in (50,68)],
                dependencies={str(Path(module.__file__).name):hashlib.sha256(Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (selector,selector.kernel)},
                scope='Complete typing of two independent native Boolean streams and their complements; no universal controller or input bridge',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','dependencies')},indent=2))
