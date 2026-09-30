"""Complete56 independent native fields, with paid bounds and even parity."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_three_selector_53 as selector

OUTER = [(f'bound{i}','+',f'F{i}',f'alpha{i}') for i in range(4)]+[
    ('p0','*','q','F3'),('p1','+','F2','p0'),('p2','*','q','p1'),
    ('p3','+','F1','p2'),('p4','*','q','p3'),('packed','+','F0','p4'),
    ('q2','*','q','q'),('n2','*','q2','q2'),('even_r','*',2,'nu')]
EXPOSE_H = [('twice_H','+','Hrep','Hrep'),('q_calc','+','twice_H',1)]


def independent_sources(z,repunit):
    q=z['q'];F=[z[f'F{i}'] for i in range(4)]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=(z[n] for n in selector.CORE_NAMES)
    X,Y=w*q**4,s*q**4;discriminant=a*a+6*a+8;u=2*r+1+j*c
    outer=[F[i]+z[f'alpha{i}']-q for i in range(4)]
    outer += [r-F[0]-q*F[1]-q*q*F[2]-q**3*F[3],r-2*z['nu']]
    if repunit:outer += [q-2*z['Hrep']-1]
    return outer+[
            ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(6*a+8),
            d*d-1-discriminant*c*c,(i*c*c)**2-discriminant*(f*f-1),
            discriminant*(f*f-1)*(u*u-ya*ya)-(1-ya*ya),u-c-o*f]


def source_check(repunit=False):
    parameters=['q','F0','F1','F2','F3']
    auxiliaries=selector.CORE_NAMES+[f'alpha{i}' for i in range(4)]+['nu']+(['Hrep'] if repunit else [])
    z={n:sp.Symbol(n) for n in parameters+auxiliaries}
    schedule=OUTER+(EXPOSE_H if repunit else [])+selector.CORE
    env=selector.execute(schedule,z)
    equalities=[(f'bound{i}','q') for i in range(4)]+[('r','packed'),('r','even_r')]
    if repunit:equalities += [('q','q_calc')]
    equalities+=selector.kernel.EQUALITIES[1:]
    sources=independent_sources(z,repunit);u=2*z['r']+1+z['j']*z['c']
    norm_index=len(sources)-3;correction=sources[norm_index]*(u*u-z['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if ix==norm_index+1 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,(repunit,ix)
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==56+2*repunit and counts['*']==31 and counts['+']+counts['-']==25+2*repunit
    assert len(equalities)==len(sources)==16+repunit and len(auxiliaries)==22+repunit
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=len(schedule),multiplications=31,additions_subtractions=25+2*repunit,equations=len(sources),
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def packed(fields,q):
    return sum(F*q**i for i,F in enumerate(fields))


def native(F,t):
    return all(F//3**j%3 in (1,2) for j in range(t))


def prepower():
    checked=0
    for q in range(2,14):
        scale=q**4
        for fields in product(range(1,q),repeat=4):
            r=packed(fields,q)
            assert r>=q**3+q*q+q+1>=15 and r<scale and scale>=16
            assert scale<r*r and scale*scale>r+1
            assert scale*(scale+1)>2*r+1 and scale*(scale+1)>12*r
            checked+=1
    return dict(positive_bounded_field_tuples=checked,minimum_q=2,maximum_q=13,
                scope='Pre-power inequalities include oddr before the paid parity comparison')


def exhaustive_fields():
    records=[]
    for t in range(1,4):
        q=3**t;scale=q**4
        checked=accepted=odd_native=0
        for fields in product(range(1,q),repeat=4):
            r=packed(fields,q)
            valuation=selector.factorial_valuation(2*r)-2*selector.factorial_valuation(r)
            native_mask=all(native(F,t) for F in fields) and fields[0]%3==2
            assert (valuation>=4*t)==native_mask,(t,fields,r,valuation)
            arithmetic=valuation>=4*t and r%2==0
            semantic=native_mask and sum(fields)%2==0
            assert arithmetic==semantic
            if arithmetic:
                assert valuation==4*t
                accepted+=1
            odd_native+=native_mask and r%2==1
            checked+=1
        assert accepted==odd_native==2**(4*t-2)
        records.append(dict(t=t,positive_bounded_tuples=checked,accepted_even_native=accepted,
                            native_words_rejected_by_explicit_parity=odd_native))
    return records


def canonical_fields():
    checked=zero_decoded=0
    for t in range(1,5):
        q=3**t;H=(q-1)//2
        for tail in product((0,1),repeat=4*t-1):
            bits=(1,)+tail
            if sum(bits)%2:continue
            T=[sum(bits[i*t+j]*3**j for j in range(t)) for i in range(4)]
            fields=[H+Ti for Ti in T];r=packed(fields,q)
            assert r%2==0 and all(F>0 and q-F>0 for F in fields)
            assert selector.factorial_valuation(2*r)-2*selector.factorial_valuation(r)==4*t
            checked+=1;zero_decoded+=sum(Ti==0 for Ti in T)
    return dict(independent_native_field_tuples=checked,identically_zero_decoded_words=zero_decoded,maximum_t=4)


def verify():
    return dict(status='PASS_COMPLETE_INDEPENDENT_NATIVE_FIELDS_56_58',
                sources={'56':source_check(),'58':source_check(True)},
                prepower=prepower(),field_scan=exhaustive_fields(),canonical=canonical_fields(),
                actual_module_kernel_case=selector.kernel.check_canonical_ratio(44),
                dependencies={Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (selector,selector.kernel)},
                scope='Four native positive fields with paid bounds and explicit even parity; no universal controller or input bridge',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('sources','dependencies')},indent=2))
