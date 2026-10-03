"""Complete53 native ternary three-selector component, not universal."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parents[1] / 'verification'
sys.path.insert(0, str(VERIFICATION))
import sympy as sp
import explore_base_three_positive_kernel as kernel

CORE = list(kernel.CORE)
CORE_NAMES = list(kernel.CORE_NAMES)
COMMON = [('p0', '*', 'q', 'F2'), ('p1', '+', 'F1', 'p0'),
          ('p2', '*', 'q', 'p1'), ('packed', '+', 'F0', 'p2'),
          ('q2', '*', 'q', 'q'), ('n2', '*', 'q2', 'q')]
OUTER53 = [('sum01', '+', 'F0', 'F1'), ('sum012', '+', 'sum01', 'F2'),
           ('checksum', '+', 'sum012', 2), ('twice_q', '+', 'q', 'q')] + COMMON
OUTER54 = [('twice_H', '+', 'Hrep', 'Hrep'), ('q_calc', '+', 'twice_H', 1),
           ('four_H', '+', 'twice_H', 'twice_H'), ('sum01', '+', 'F0', 'F1'),
           ('sum012', '+', 'sum01', 'F2')] + COMMON


def execute(rows, inputs):
    env = dict(inputs)
    for name, op, a, b in rows:
        assert name not in env
        left = env[a] if isinstance(a, str) else a
        right = env[b] if isinstance(b, str) else b
        env[name] = left*right if op == '*' else left+right if op == '+' else left-right
    return env


def sources(z, repunit):
    q, F0, F1, F2 = (z[v] for v in ('q','F0','F1','F2'))
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya = (z[v] for v in CORE_NAMES)
    X,Y = w*q**3,s*q**3
    D = a*a+6*a+8
    u = 2*r+1+j*c
    prefix = [q-2*z['Hrep']-1, F0+F1+F2-4*z['Hrep']] if repunit else [F0+F1+F2+2-2*q]
    return prefix + [
        r-F0-q*F1-q*q*F2,
        ((X*Y)**2+X)*(Y*k)**2-tau*(tau+1),
        c-Y*k-eta, k-eta-zeta, k-r-1-h*X*Y,
        a-Y*(X+1), d-X-a*c-ga*(6*a+8),
        d*d-1-D*c*c, (i*c*c)**2-D*(f*f-1),
        D*(f*f-1)*(u*u-ya*ya)-(1-ya*ya), u-c-o*f,
    ]


def source_check(repunit=False):
    names = ['q','F0','F1','F2']+CORE_NAMES+(['Hrep'] if repunit else [])
    z = {name: sp.Symbol(name) for name in names}
    outer = OUTER54 if repunit else OUTER53
    schedule = outer+CORE
    env = execute(schedule,z)
    equalities = ([('q','q_calc'),('sum012','four_H')] if repunit else [('checksum','twice_q')])
    equalities += [('r','packed')]+kernel.EQUALITIES[1:]
    polynomials = sources(z,repunit)
    aux_index = len(polynomials)-3
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[aux_index]*(u*u-z['y_aux']**2)
    records = []
    for ix, ((left,right), p) in enumerate(zip(equalities,polynomials)):
        actual = env[left]-env[right]
        adjust = correction if ix == len(polynomials)-2 else 0
        assert sp.expand(actual-p-adjust) == 0, ix
        records.append(dict(equality=[left,right],source=str(sp.expand(p)),correction=str(sp.expand(adjust))))
    count = Counter(row[1] for row in schedule)
    assert len(schedule) == 53+repunit
    assert count['*'] == 29 and count['+']+count['-'] == 24+repunit
    assert len(equalities) == len(polynomials) == 12+repunit
    used = {v for row in schedule for v in row[2:] if isinstance(v,str)}
    used |= {v for row in equalities for v in row}
    assert set(names) <= used
    return dict(operations=len(schedule),multiplications=count['*'],additions_subtractions=count['+']+count['-'],
                positive_parameters=['q','F0','F1','F2'],positive_auxiliaries=CORE_NAMES+(['Hrep'] if repunit else []),
                equations=len(equalities),instructions=[list(row) for row in schedule],sources=records)


def factorial_valuation(n):
    result = 0
    while n:
        n //= 3
        result += n
    return result


def valuation(n):
    return factorial_valuation(2*n)-2*factorial_valuation(n)


def native(f,t):
    return 0<f<3**t and all(f//3**j % 3 in (1,2) for j in range(t))


def prepower_check():
    count = 0
    for q in range(3,41):
        scale = q**3
        for F0 in range(1,2*q-3):
            for F1 in range(1,2*q-2-F0):
                F2 = 2*q-2-F0-F1
                if F2 <= 0:
                    continue
                P = F0+q*F1+q*q*F2
                assert q*q<P<2*scale
                assert scale>=27 and P>=13 and scale<P*P
                assert scale*scale>P+1 and scale*(scale+1)>2*P+1
                assert 12*P < scale*(scale+1) # 6r/a<1/2 at minimal a.
                assert P+2>=15
                assert (2*(scale*(scale+1)+3)-1)**14 > (scale*(scale+1)+3)**6
                count += 1
    return dict(arbitrary_q_triples=count,q_min=3,q_max=40,min_scale=27,min_index_bound=13)


def exhaustive_fields():
    cases = accepted = field_overflow = packed_overflow = 0
    rows = []
    for t in range(1,6):
        q = 3**t
        subtotal = found = 0
        for F0 in range(1,2*q-3):
            for F1 in range(1,2*q-2-F0):
                F2 = 2*q-2-F0-F1
                if F2 <= 0:
                    continue
                fields = (F0,F1,F2)
                P = F0+q*F1+q*q*F2
                arithmetic = valuation(P) >= 3*t
                semantic = all(native(f,t) for f in fields) and F0 % 3 == 2
                assert arithmetic == semantic, (t,fields,P,valuation(P))
                if arithmetic:
                    H = (q-1)//2
                    assert all(sum((f-H)//3**j % 3 for f in fields)==1 for j in range(t))
                    assert P%2 == 0 and valuation(P) == 3*t
                    found += 1
                field_overflow += max(fields)>=q
                packed_overflow += P>=q**3
                subtotal += 1
        assert found == 3**(t-1)
        cases += subtotal
        accepted += found
        rows.append(dict(t=t,q=q,cases=subtotal,accepted=found))
    return dict(cases=cases,accepted=accepted,field_overflow=field_overflow,packed_overflow=packed_overflow,domains=rows)


def canonical_selectors():
    count = zero_selectors = 0
    for t in range(1,8):
        q = 3**t
        H = (q-1)//2
        for tail in product(range(3),repeat=t-1):
            labels = (0,)+tail
            T = [sum(3**j for j,label in enumerate(labels) if label==i) for i in range(3)]
            fields = [H+v for v in T]
            P = sum(f*q**i for i,f in enumerate(fields))
            assert min(fields)>0 and sum(fields)+2==2*q and P%2==0
            assert valuation(P)==3*t
            for perm in ((0,1,2),(2,0,1),(1,2,0)):
                projected = H+fields[perm.index(2)]-fields[perm.index(0)]
                wanted = sum(perm[label]*3**j for j,label in enumerate(labels))
                assert projected == wanted
            zero_selectors += sum(v==0 for v in T)
            count += 1
    return dict(histories=count,zero_decoded_selectors=zero_selectors,max_t=7)


def sha(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def verify():
    return dict(scope='Complete native selector relation; universal controller/input/FIFO composition unpaid; universal bound remains76',
                module53=source_check(),module54=source_check(True),prepower=prepower_check(),
                exhaustive_fields=exhaustive_fields(),canonical=canonical_selectors(),
                canonical_ratio=[kernel.check_canonical_ratio(r) for r in (14,16)],
                auxiliary_pell_values_materialized=False,
                dependencies={name:sha(VERIFICATION/name) for name in ('explore_base_three_positive_kernel.py',)})


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key not in ('module53','module54')},indent=2))
