"""Exact even-length NAE/majority60 with one bound on the packed word."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_nae_majority61 as prior

selector=prior.selector
OUTER=[('twice_H','+','Hrep','Hrep'),('q_calc','+','twice_H',1),
       ('p0','*','q','F1'),('packed','+','F0','p0'),('n2','*','q','q'),
       ('packed_bound','+','r','alpha')]
EXTRA=list(prior.EXTRA)


def source_check():
    parameters=['q','F0','F1','R0','R1']
    auxiliaries=['Hrep','alpha']+selector.CORE_NAMES+['portA','portB','K0','K1','Z0','Z1']
    z={name:sp.Symbol(name) for name in parameters+auxiliaries}
    schedule=OUTER+selector.CORE+EXTRA
    env=selector.execute(schedule,z)
    equalities=[('q','q_calc'),('packed_bound','n2'),('r','packed')]
    equalities+=selector.kernel.EQUALITIES[1:]
    equalities += [('gate','F1'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]
    previous=prior.independent_sources(dict(z,alpha0=sp.Integer(0),alpha1=sp.Integer(0)))
    sources=[previous[0],z['r']+z['alpha']-z['q']**2]+previous[3:]
    u=2*z['r']+1+z['j']*z['c'];correction=sources[10]*(u*u-z['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if index==11 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,index
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==60 and counts['*']==33 and counts['+']+counts['-']==27
    assert len(equalities)==len(sources)==18 and len(auxiliaries)==25
    assert len(set(parameters+auxiliaries))==len(parameters+auxiliaries)
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=60,multiplications=33,additions_subtractions=27,equations=18,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records,
                explicit_individual_field_bounds=False,explicit_parity_or_square_width=False)


def prepower_and_typing():
    prepower=0
    for H in range(2,41):
        q=2*H+1;scale=q*q
        for F1 in range(1,q):
            for F0 in range(1,min(scale-q*F1,F1+H-1)):
                r=F0+q*F1
                assert q+1<=r<scale<r*r
                assert 0<F0<=F1+H-2<=q+H-3<2*q
                assert scale>=25 and r>=6 and scale*(scale+1)>12*r
                prepower+=1
    records=[]
    for t in range(1,6):
        q,H=3**t,(3**t-1)//2
        checked=carry_candidates=accepted=0
        for F1 in range(1,q):
            for F0 in range(1,min(q*q-q*F1,F1+H-1)):
                P=F0+q*F1
                arithmetic=selector.valuation(P)>=2*t
                semantic=prior.prior.pairs.native(F0,t) and prior.prior.pairs.native(F1,t) and F0%3==2
                assert arithmetic==semantic,(t,F0,F1,P)
                if F0>=q:
                    assert F0-q<=H-3<H+1
                    assert not arithmetic
                    carry_candidates+=1
                accepted+=arithmetic;checked+=1
        records.append(dict(t=t,positive_field_candidates=checked,
                            candidates_with_low_field_carry=carry_candidates,typed_accepted=accepted))
    # A packed bound alone is insufficient without the gate-derived estimate.
    q,H,F0,F1=9,4,14,4;P=F0+q*F1
    assert 0<P<q*q and P%2==0 and selector.valuation(P)==4
    assert F0>=q and H+F1-F0<2
    return dict(prepower_positive_field_tuples=prepower,maximum_H=40,field_scan=records,
                packing_only_false_field=dict(q=q,H=H,F0=F0,F1=F1,P=P,alpha=q*q-P,
                                             reason='Fails the retained positive-port gate; not a counterexample to60'))


def canonical_outer(digits,a,b):
    previous=prior.canonical_outer(digits,a,b)
    values=dict(previous['values'])
    del values['alpha0'];del values['alpha1']
    values['r']=previous['r'];values['alpha']=values['q']**2-values['r']
    assert min(values.values())>0
    env=selector.execute(OUTER+EXTRA,values)
    for left,right in [('q','q_calc'),('packed_bound','n2'),('r','packed'),
                       ('gate','F1'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]:
        assert env[left]==env[right]
    previous['values']=values
    return previous


def positive_lifts():
    checked=0
    for t in range(2,9,2):
        mask=(1<<t)-1
        for high in range(1<<(t-1)):
            d=1+(high<<1)
            for a,b in product(range(1,t+1),repeat=2):
                A=((d>>a)|(d<<(t-a)))&mask
                B=((d>>b)|(d<<(t-b)))&mask
                if (d|A|B)==mask and d&A&B==0:
                    canonical_outer(tuple((d>>j)&1 for j in range(t)),a,b)
                    checked+=1
    return dict(positive_even_length_outer_lifts=checked,maximum_t=8)


def verify():
    return dict(status='PASS_COMPLETE_EVEN_LENGTH_NAE_MAJORITY_60',source=source_check(),
                bounds_and_typing=prepower_and_typing(),positive_lifts=positive_lifts(),
                examples=[canonical_outer((1,0),1,1),canonical_outer((1,0),2,1),
                          canonical_outer((1,1,0,0,0,0),2,4)],
                dependencies={str(Path(module.__file__).name):hashlib.sha256(
                    Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (prior,prior.prior,selector,selector.kernel)},
                scope='Exact even-length NAE/majority component using gate-derived field bound; not a universal compiler',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','dependencies')},indent=2))
