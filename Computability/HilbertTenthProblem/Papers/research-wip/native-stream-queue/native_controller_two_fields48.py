"""Complete48/50 two-field typing, with optional paid-parity49/51 variants."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_three_selector_53 as selector

OUTER=[('bound0','+','F0','alpha0'),('bound1','+','F1','alpha1'),
       ('pack_product','*','q','F1'),('packed','+','F0','pack_product'),
       ('n2','*','q','q'),('even_r','*',2,'nu')]
EXPOSE_H=[('twice_H','+','Hrep','Hrep'),('q_calc','+','twice_H',1)]


def independent_sources(z,repunit,paid_parity=True):
    q,F0,F1=z['q'],z['F0'],z['F1']
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=(z[n] for n in selector.CORE_NAMES)
    X,Y=w*q*q,s*q*q;discriminant=a*a+6*a+8;u=2*r+1+j*c
    outer=[F0+z['alpha0']-q,F1+z['alpha1']-q,r-F0-q*F1]
    if paid_parity:outer += [r-2*z['nu']]
    if repunit:outer += [q-2*z['Hrep']-1]
    return outer+[
            ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(6*a+8),
            d*d-1-discriminant*c*c,(i*c*c)**2-discriminant*(f*f-1),
            discriminant*(f*f-1)*(u*u-ya*ya)-(1-ya*ya),u-c-o*f]


def source_check(repunit=False,paid_parity=True):
    parameters=['q','F0','F1']
    auxiliaries=selector.CORE_NAMES+['alpha0','alpha1']+(['nu'] if paid_parity else [])+(['Hrep'] if repunit else [])
    z={n:sp.Symbol(n) for n in parameters+auxiliaries}
    schedule=(OUTER if paid_parity else OUTER[:-1])+(EXPOSE_H if repunit else [])+selector.CORE
    env=selector.execute(schedule,z)
    equalities=[('bound0','q'),('bound1','q'),('r','packed')]
    if paid_parity:equalities += [('r','even_r')]
    if repunit:equalities += [('q','q_calc')]
    equalities+=selector.kernel.EQUALITIES[1:]
    sources=independent_sources(z,repunit,paid_parity);u=2*z['r']+1+z['j']*z['c']
    norm_index=len(sources)-3;correction=sources[norm_index]*(u*u-z['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if ix==norm_index+1 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,(repunit,ix)
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==48+paid_parity+2*repunit and counts['*']==27+paid_parity and counts['+']+counts['-']==21+2*repunit
    assert len(equalities)==len(sources)==13+paid_parity+repunit and len(auxiliaries)==19+paid_parity+repunit
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=len(schedule),multiplications=27+paid_parity,additions_subtractions=21+2*repunit,equations=len(sources),
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def prepower():
    checked=excluded_even_q=naive_ratio_failures=0
    for q in range(2,41):
        scale=q*q
        for F0,F1 in product(range(1,q),repeat=2):
            r=F0+q*F1
            if q%2==0:
                excluded_even_q+=1
                continue
            assert q>=3 and scale>=9 and q+1<=r<scale and r>=4
            assert scale<r*r and scale*scale>r+1 and scale*(scale+1)>2*r+1
            assert r+2>=6
            # The initial crude estimate need not prove12r<a; lower ratio comes first.
            naive_ratio_failures+=12*r>=scale*(scale+1)
            improved_a=(scale+1)*scale**r
            assert improved_a>scale**(r+1)>12*r
            checked+=1
    A=sp.Symbol('A')
    psi6=32*A**5-32*A**3+6*A
    gap=sp.expand(psi6-A*(A*A-1)**2)
    assert gap==31*A**5-30*A**3+5*A
    assert excluded_even_q>0 and naive_ratio_failures==1
    return dict(odd_radix_bounded_field_tuples=checked,excluded_even_radix_tuples=excluded_even_q,
                cases_requiring_reordered_ratio_bound=naive_ratio_failures,
                minimum_q_after_even_radix_exclusion=3,maximum_q=40,
                rank_gap_at_index6=str(gap),
                note='At q3,r8 the crude a>=90 estimate is insufficient; the lower-ratio improvement supplies the required upper-ratio hypothesis.')


def exhaustive_fields():
    records=[]
    for t in range(1,7):
        q=3**t;checked=accepted=odd_native=0
        for F0,F1 in product(range(1,q),repeat=2):
            r=F0+q*F1
            valuation=selector.factorial_valuation(2*r)-2*selector.factorial_valuation(r)
            typed=F0%3==2 and all(F//3**j%3 in (1,2) for F in (F0,F1) for j in range(t))
            assert (valuation>=2*t)==typed,(t,F0,F1,r,valuation)
            assert (valuation>=2*t and r%2==0)==(typed and (F0+F1)%2==0)
            accepted+=typed and r%2==0;odd_native+=typed and r%2==1
            checked+=1
        assert accepted==odd_native==2**(2*t-2)
        records.append(dict(t=t,positive_bounded_field_pairs=checked,accepted_even_native=accepted,
                            native_pairs_excluded_by_index_parity=odd_native))
    return records


def canonical_pairs():
    checked=zero_decoded=0
    for t in range(1,8):
        q=3**t;H=(q-1)//2
        for tail in product((0,1),repeat=2*t-1):
            bits=(1,)+tail
            if sum(bits)%2:continue
            U=sum(bits[j]*3**j for j in range(t));V=sum(bits[t+j]*3**j for j in range(t))
            F0,F1=H+U,H+V;r=F0+q*F1
            assert all(0<F<q for F in (F0,F1)) and r%2==0
            assert selector.factorial_valuation(2*r)-2*selector.factorial_valuation(r)==2*t
            checked+=1;zero_decoded+=(U==0)+(V==0)
    return dict(independent_boolean_pairs=checked,identically_zero_decoded_words=zero_decoded,maximum_t=7)


def verify():
    return dict(status='PASS_COMPLETE_TWO_NATIVE_FIELDS_48_50_WITH_PAID_PARITY_VARIANTS',
                sources={str(48+paid+2*repunit):source_check(repunit,paid) for paid in (False,True) for repunit in (False,True)},
                prepower=prepower(),field_scan=exhaustive_fields(),canonical=canonical_pairs(),
                actual_smallest_module_kernel_case=selector.kernel.check_canonical_ratio(8),
                dependencies={Path(module.__file__).name:hashlib.sha256(Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (selector,selector.kernel)},
                scope='Two independent native fields with paid bounds and proved implicit even parity; optional explicit-parity sources retained; no controller or ordinary-input bridge',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('sources','dependencies')},indent=2))
