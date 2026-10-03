"""Exact even-length cyclic NAE/majority relation in61 operations."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_nae_majority67 as prior

selector = prior.selector
OUTER = [
    ('twice_H','+','Hrep','Hrep'),('q_calc','+','twice_H',1),
    ('bound0','+','F0','alpha0'),('bound1','+','F1','alpha1'),
    ('p0','*','q','F1'),('packed','+','F0','p0'),('n2','*','q','q')]
EXTRA = list(prior.EXTRA)


def independent_sources(z):
    q,H,F0,F1 = (z[name] for name in ('q','Hrep','F0','F1'))
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya = (z[n] for n in selector.CORE_NAMES)
    X,Y = w*q*q,s*q*q
    disc = a*a+6*a+8;u = 2*r+1+j*c;Dword = F0-H
    return [q-2*H-1,F0+z['alpha0']-q,F1+z['alpha1']-q,r-F0-q*F1,
            ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(6*a+8),
            d*d-1-disc*c*c,(i*c*c)**2-disc*(f*f-1),
            disc*(f*f-1)*(u*u-ya*ya)-(1-ya*ya),u-c-o*f,
            z['portA']+z['portB']+Dword-F1,
            z['R0']*z['portA']-Dword-2*H*z['K0'],q-z['R0']*z['Z0'],
            z['R1']*z['portB']-Dword-2*H*z['K1'],q-z['R1']*z['Z1']]


def source_check():
    parameters = ['q','F0','F1','R0','R1']
    auxiliaries = ['Hrep','alpha0','alpha1']+selector.CORE_NAMES+['portA','portB','K0','K1','Z0','Z1']
    z = {name:sp.Symbol(name) for name in parameters+auxiliaries}
    schedule = OUTER+selector.CORE+EXTRA
    env = selector.execute(schedule,z)
    equalities = [('q','q_calc'),('bound0','q'),('bound1','q'),('r','packed')]
    equalities += selector.kernel.EQUALITIES[1:]
    equalities += [('gate','F1'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]
    sources = independent_sources(z);u = 2*z['r']+1+z['j']*z['c']
    correction = sources[11]*(u*u-z['y_aux']**2)
    records = []
    for index,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust = correction if index == 12 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0,index
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 61 and counts['*'] == 33 and counts['+']+counts['-'] == 28
    assert len(equalities) == len(sources) == 19 and len(auxiliaries) == 26
    assert len(set(parameters+auxiliaries)) == len(parameters+auxiliaries)
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    return dict(operations=61,multiplications=33,additions_subtractions=28,equations=19,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records,
                explicit_parity_or_square_width_instruction=False)


def prepower():
    checked = 0
    for H in range(2,61):
        q=2*H+1;scale=q*q
        for F0,F1 in product(range(1,q),repeat=2):
            r=F0+q*F1
            assert q>=5 and scale>=25 and q+1<=r<scale and scale<r*r
            assert scale*scale>r+1 and scale*(scale+1)>2*r+1
            assert scale*(scale+1)>12*r
            assert r+2>=8
            checked+=1
    # Exhaust all q=3 positive fields and ports; no appeal to Pell parity.
    q3_candidates = 0
    for F0,F1 in product((1,2),repeat=2):
        D=F0-1
        for A in range(1,F1-D):
            B=F1-D-A
            assert A>0 and B>0
            for R0,R1 in product((1,3),repeat=2):
                num0,num1=R0*A-D,R1*B-D
                assert not (num0>0 and num1>0 and num0%2==num1%2==0)
                q3_candidates+=1
    assert q3_candidates>0
    return dict(positive_bounded_field_tuples=checked,maximum_H=60,
                q3_positive_outer_candidates=q3_candidates,
                scope='Pre-power bounds and q3 exclusion, without assuming field typing or packed parity')


def field_typing():
    rows=[]
    for t in range(1,6):
        q=3**t;checked=accepted=0
        for F0,F1 in product(range(1,q),repeat=2):
            r=F0+q*F1
            valuation=selector.valuation(r)
            native=prior.pairs.native(F0,t) and prior.pairs.native(F1,t) and F0%3==2
            assert (valuation>=2*t)==native
            checked+=1;accepted+=native
        rows.append(dict(t=t,positive_field_tuples=checked,native_accepted=accepted))
    return rows


def canonical_outer(digits,a,b):
    t=len(digits);assert t>=2 and t%2==0
    q,H=3**t,(3**t-1)//2
    ad,bd=digits[a:]+digits[:a],digits[b:]+digits[:b]
    sums=tuple(x+y+z for x,y,z in zip(digits,ad,bd))
    assert digits[0]==1 and all(total in (1,2) for total in sums)
    vd=tuple(total-1 for total in sums)
    D,V,A,B=prior.word(digits),prior.word(vd),prior.word(ad),prior.word(bd)
    F0,F1=H+D,H+V
    values=dict(q=q,Hrep=H,F0=F0,F1=F1,alpha0=q-F0,alpha1=q-F1,
                R0=3**a,R1=3**b,portA=A,portB=B,K0=D%3**a,K1=D%3**b,
                Z0=3**(t-a),Z1=3**(t-b))
    assert min(values.values())>0
    env=selector.execute(OUTER+EXTRA,values)
    for left,right in [('q','q_calc'),('bound0','q'),('bound1','q'),
                       ('gate','F1'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]:
        assert env[left]==env[right]
    r=env['packed']
    assert (D+V)%2==H%2==r%2==0
    assert selector.valuation(r)==2*t
    return dict(values=values,D=list(digits),A=list(ad),B=list(bd),V=list(vd),r=r,
                kernel_witnesses='Retained positive plus-branch converse at scale q squared; not materialized')


def gate_parity_and_lifts():
    checked=admitted=even=odd=zero_v=0
    example_zero=None
    for t in range(1,13):
        mask=(1<<t)-1
        for tail in range(1<<(t-1)):
            d=1+(tail<<1)
            for a,b in product(range(1,t+1),repeat=2):
                A=((d>>a)|(d<<(t-a)))&mask
                B=((d>>b)|(d<<(t-b)))&mask
                checked+=1
                if (d|A|B)!=mask or (d&A&B)!=0:
                    continue
                admitted+=1
                majority=(d&A)|(d&B)|(A&B)
                # Ternary numeric parity is bit-population parity.
                packed_parity=(d.bit_count()+majority.bit_count())%2
                assert packed_parity==t%2
                if t%2:
                    odd+=1
                else:
                    even+=1;zero_v+=majority==0
                    if t<=8:
                        record=canonical_outer(tuple((d>>j)&1 for j in range(t)),a,b)
                        if majority==0 and example_zero is None:example_zero=record
    assert even>0 and odd>0 and zero_v>0 and example_zero is not None
    return dict(boolean_word_offset_candidates=checked,NAE_admitted=admitted,
                even_length_admitted=even,odd_length_excluded_by_kernel_parity=odd,
                maximum_t=12,positive_outer_lift_maximum_t=8,zero_majority_cases=zero_v,
                zero_majority_example=example_zero,
                scope='The necessity of even packed r uses the proved generic signed-parity theorem, not a numerical full-Pell enumeration')


def rotation_closure():
    # Exact Laurent-polynomial identity behind the spectral lemma.
    x,y=sp.symbols('x y')
    assert sp.expand(x*y*((1+x+y)*(1+1/x+1/y)-1)-(1+x)*(1+y)*(x+y))==0
    checked=closed=0;mixture=None
    for t in range(2,13,2):
        mask=(1<<t)-1
        rot=lambda value,a:((value>>a)|(value<<(t-a)))&mask
        for high in range(1<<(t-1)):
            d=1+(high<<1)
            for a,b in product(range(1,t+1),repeat=2):
                A,B=rot(d,a),rot(d,b)
                if (d|A|B)!=mask or d&A&B:
                    continue
                v=(d&A)|(d&B)|(A&B)
                for e in range(1,t+1):
                    checked+=1
                    if rot(d,e)!=v:
                        continue
                    closed+=1
                    assert d.bit_count()*2==t
                    spin=tuple(2*((d>>j)&1)-1 for j in range(t))
                    shift=lambda row,s:tuple(row[(j+s)%t] for j in range(t))
                    add=lambda row,other:tuple(x+y for x,y in zip(row,other))
                    first=add(shift(spin,a),shift(spin,b))
                    second=add(first,shift(first,b))
                    annihilated=add(second,shift(second,a))
                    assert not any(annihilated)
                    if mixture is None and all(pair!=mask for pair in (d^A,d^B,A^B)):
                        mixture=dict(t=t,a=a,b=b,e=e,D=[(d>>j)&1 for j in range(t)])
    # Arbitrarily many free bits remain in a single cancellation branch:
    # t=2m, a=m, e=b and d_(j+m)=1-d_j.
    free_cases=0
    for m in range(1,9):
        t=2*m;mask=(1<<t)-1
        for high in range(1<<(m-1)):
            half=1+(high<<1)
            d=half|((((1<<m)-1)^half)<<m)
            for b in (1,t):
                rot=lambda value,s:((value>>s)|(value<<(t-s)))&mask
                A,B=rot(d,m),rot(d,b)
                assert d^A==mask
                assert (d|A|B)==mask and d&A&B==0
                assert ((d&A)|(d&B)|(A&B))==B
                free_cases+=1
    # Two invariant residue classes can use different cancellation branches.
    # This is a construction, not an inference from the bounded search above.
    t,a,b,e=60,6,16,40
    digits=tuple(int((j//2)%(6 if j%2==0 else 10)<(3 if j%2==0 else 5)) for j in range(t))
    shifted=lambda h:tuple(digits[(j+h)%t] for j in range(t))
    Aword,Bword,Vword=shifted(a),shifted(b),shifted(e)
    assert all(d+A+B==1+V for d,A,B,V in zip(digits,Aword,Bword,Vword))
    assert not any(all(x+y==1 for x,y in zip(left,right)) for left,right in
                   ((digits,Aword),(digits,Bword),(Aword,Bword)))
    mixed_constructed=dict(t=t,a=a,b=b,e=e,D=list(digits))
    return dict(closure_offset_candidates=checked,admitted=closed,maximum_t=12,
                exact_factor_identity=True,annihilating_operator_checked=True,
                balanced_population_checked=True,free_half_word_cases=free_cases,
                maximum_free_half_length=8,small_scan_mixed_example=mixture,
                constructed_mixed_cancellation_example=mixed_constructed,
                scope='Structural consequence conditional on an additional rotation closure; the61 source itself does not impose that closure')


def verify():
    actual_kernel=[]
    for r in (50,68):
        X=3**(2*r+1);Y=(X+1)**(2*r)//X**r
        assert X%81==Y%81==0
        actual_kernel.append(dict(q=9,scale=81,**selector.kernel.check_canonical_ratio(r)))
    return dict(status='PASS_COMPLETE_EVEN_LENGTH_NAE_MAJORITY_61',source=source_check(),
                prepower=prepower(),field_typing=field_typing(),gate=gate_parity_and_lifts(),
                examples=[canonical_outer((1,0),1,1),canonical_outer((1,0),2,1)],
                actual_main_first_kernel_cases=actual_kernel,
                rotation_closure=rotation_closure(),
                dependencies={str(Path(module.__file__).name):hashlib.sha256(
                    Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (prior,prior.pairs,selector,selector.kernel)},
                scope='Exact even-length cyclic NAE/majority relation; no ordinary input or universal compiler',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','dependencies')},indent=2))
