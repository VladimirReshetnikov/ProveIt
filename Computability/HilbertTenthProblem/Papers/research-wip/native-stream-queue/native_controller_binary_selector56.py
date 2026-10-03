"""Exact four-way binary one-hot selector in56 operations; not universal."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path
import sys
import sympy as sp

HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parents[1] / 'verification'
sys.path.insert(0, str(VERIFICATION))
import explore_fixed_raw_universal_78 as retained
import native_controller_three_selector_53 as ternary

CORE_NAMES = list(ternary.CORE_NAMES)
CORE = list(retained.CORE)
CORE_EQUALITIES = list(retained.EQUALITIES[6:16])
OUTER = [('bs_p0', '*', 'q', 'F3'), ('bs_p1', '+', 'F2', 'bs_p0'),
         ('bs_p2', '*', 'q', 'bs_p1'), ('bs_p3', '+', 'F1', 'bs_p2'),
         ('bs_p4', '*', 'q', 'bs_p3'), ('bs_packed', '+', 'F0', 'bs_p4'),
         ('bs_sum01', '+', 'F0', 'F1'), ('bs_sum012', '+', 'bs_sum01', 'F2'),
         ('bs_Q', '+', 'bs_sum012', 'F3'), ('bs_q', '+', 'bs_Q', 1),
         ('bs_even', '*', 2, 'odd_half'), ('bs_odd', '+', 'bs_even', 1)]
BOUND = [('bs_X_bound', '+', 'r', 'bound_beta')]


def independent_sources(z):
    q, f0, f1, f2, f3 = (z[name] for name in ('q', 'F0', 'F1', 'F2', 'F3'))
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y = (z[name] for name in CORE_NAMES)
    X,Y = w*q,s*q
    delta = a*a+4*a+3
    u = j*c-(2*r+1)
    return [r-f0-q*f1-q*q*f2-q*q*q*f3,
            f0+f1+f2+f3+1-q,
            s-2*z['odd_half']-1,
            r+z['bound_beta']-X,
            ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
            c-Y*k-eta, k-eta-zeta, k-r-1-h*X*Y,
            a-Y*(X+1), d-X-a*c-ga*(4*a+3),
            d*d-1-delta*c*c, (i*c*c)**2-delta*(f*f-1),
            delta*(f*f-1)*(u*u-y*y)-(1-y*y), u+c-o*f]


def source_check(gate=False):
    parameters = ['q', 'F0', 'F1', 'F2', 'F3']
    auxiliaries = CORE_NAMES+['odd_half', 'bound_beta']
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries}
    schedule = OUTER+CORE+BOUND+([('bs_input_A', '+', 'F1', 'F3'),
                                   ('bs_input_B', '+', 'F2', 'F3')] if gate else [])
    env = ternary.execute(schedule, dict(z, n2=z['q']))
    equalities = [('r', 'bs_packed'), ('bs_q', 'q'), ('s', 'bs_odd'),
                  ('bs_X_bound', 'wn2')]+CORE_EQUALITIES
    sources = independent_sources(z)
    u = z['j']*z['c']-(2*z['r']+1)
    correction = sources[11]*(u*u-z['y_aux']**2)
    records = []
    for index, ((left,right), source) in enumerate(zip(equalities,sources)):
        adjust = correction if index == 12 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0, index
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 56+2*gate and counts['*'] == 29 and counts['+']+counts['-'] == 27+2*gate
    if gate:
        assert sp.expand(env['bs_input_A']-z['F1']-z['F3']) == 0
        assert sp.expand(env['bs_input_B']-z['F2']-z['F3']) == 0
        assert sp.expand(env['bs_sum012']-z['F0']-z['F1']-z['F2']) == 0
    assert len(sources) == len(equalities) == 14 and len(auxiliaries) == 19
    assert set().union(*(source.free_symbols for source in sources)) == set(z.values())
    assert CORE == retained.CORE
    return dict(operations=56+2*gate,multiplications=29,additions_subtractions=27+2*gate,equations=14,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                aliases={'n2':'q'},
                gate_ports=({'input_A':'bs_input_A','input_B':'bs_input_B','output_D':'bs_sum012'} if gate else {}),
                instructions=[list(row) for row in schedule],sources=records)


def pack(q, fields):
    return sum(field*q**index for index,field in enumerate(fields))


def one_hot(q, fields):
    return all(sum(field>>bit & 1 for field in fields) == 1
               for bit in range(q.bit_length()-1))


def prepower():
    cases = 0
    for q in range(5, 31):
        for f0 in range(1,q-3):
            for f1 in range(1,q-2-f0):
                for f2 in range(1,q-1-f0-f1):
                    f3 = q-1-f0-f1-f2
                    if f3 < 1:
                        continue
                    r = pack(q,(f0,f1,f2,f3))
                    assert q**3+q*q+q+1 <= r < q**4 and r >= 156
                    # Smallest multiple of q strictly above r.
                    X = q*(r//q+1)
                    Y = 3*q  # odd_half is positive, hence s>=3.
                    E = X*Y
                    a = Y*(X+1)
                    A = a+2
                    P = 2*X*Y*Y+1
                    assert X>r and E>r+1 and a>2*r+1
                    assert P>A and 6*X*Y*Y>a and r+2>=158
                    assert 4*a+3 > X
                    cases += 1
    # Conservative post-lower-ratio estimates, checked without huge X powers.
    assert 24*156 < 2**(2*156)
    assert 6*156 < 157**157
    return dict(positive_field_tuples=cases,q_range=[5,30],minimal_r=156,
                paid_bound='r+bound_beta=X',
                note='Tests preliminary inequalities, not first/main Pell sufficiency')


def fields_audit():
    rows=[]
    for t in range(2,7):
        q=2**t
        candidates=admitted=onehot_ignoring_origin=0
        for f0 in range(1,q-3):
            for f1 in range(1,q-2-f0):
                for f2 in range(1,q-1-f0-f1):
                    f3=q-1-f0-f1-f2
                    if f3<1:
                        continue
                    fields=(f0,f1,f2,f3)
                    r=pack(q,fields)
                    exact_popcount=(r.bit_count()==t)
                    expected=one_hot(q,fields)
                    assert exact_popcount==expected
                    assert (r%2==1)==(f0%2==1)
                    candidates+=1
                    onehot_ignoring_origin+=expected
                    admitted+=expected and bool(f0%2)
        # Each of four labels occurs; the origin is fixed to label0.
        expected_origin=sum((-1)**missing*comb(3,missing)*(4-missing)**(t-1)
                            for missing in range(4))
        assert admitted==expected_origin and onehot_ignoring_origin==4*admitted
        rows.append(dict(t=t,q=q,positive_checksum_tuples=candidates,
                         onehot_without_origin=onehot_ignoring_origin,
                         admitted_with_first_label0=admitted))
    return rows


def canonical_partition_checks():
    cases=0
    for t in range(4,8):
        q=2**t
        for tail in product(range(4),repeat=t-1):
            labels=(0,)+tail
            if set(labels)!={0,1,2,3}:
                continue
            fields=tuple(sum(1<<j for j,label in enumerate(labels) if label==i)
                         for i in range(4))
            r=pack(q,fields)
            assert sum(fields)==q-1 and r%2==1 and r.bit_count()==t
            assert q<r and t<2*r+1
            input_a=fields[1]+fields[3]
            input_b=fields[2]+fields[3]
            output_d=sum(fields[:3])
            assert output_d==(q-1)^(input_a & input_b)
            assert input_a%2==input_b%2==0 and output_d%2==1
            cases+=1
    return dict(positive_partitions=cases,t_range=[4,7],
                scope='Checks all outer data; astronomical positive Pell coordinates are supplied by the proof')


def exact_valuation_prototypes():
    result=[]
    for q, fields in [(16,(1,2,4,8)),(16,(1,4,8,2)),(32,(3,4,8,16))]:
        r=pack(q,fields)
        central=comb(2*r,r)
        valuation=(central & -central).bit_length()-1
        assert valuation==r.bit_count()==q.bit_length()-1
        assert (central//q)%2==1
        # Every noncentral integer term is divisible by X and hence by2q.
        assert 2*r+1 > q.bit_length()-1
        result.append(dict(q=q,fields=list(fields),r=r,central_valuation=valuation,
                           central_over_q_mod2=(central//q)%2,
                           central_bits=central.bit_length()))
    return result


def verify():
    return dict(status='PASS_COMPLETE_BINARY_FOUR_SELECTOR56',source=source_check(),gate_source=source_check(True),
                prepower=prepower(),fields=fields_audit(),canonical=canonical_partition_checks(),
                valuation_prototypes=exact_valuation_prototypes(),
                retained_core_sha256=hashlib.sha256(json.dumps(CORE,separators=(',',':')).encode()).hexdigest(),
                exact_projection=('q=2^t; four strictly positive binary words partition the '
                                  't-position repunit, and the first bit of F0 is1. Necessarily t>=4.'),
                scope='Complete native typing component only; no wiring, controller, input bridge or universal acceptance',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key not in ('source','gate_source')},indent=2))
