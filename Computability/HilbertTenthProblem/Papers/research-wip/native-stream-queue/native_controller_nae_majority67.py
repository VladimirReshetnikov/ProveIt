"""Complete cyclic NAE/majority relation in67 operations; not universal."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_boolean_pairs56 as pairs

selector = pairs.selector
EXTRA = [
    ('Dword','-','F0','Hrep'),
    ('ports','+','portA','portB'),('gate','+','ports','Dword'),
    ('RA0','*','R0','portA'),('guard0','*','twice_H','K0'),
    ('rhs0','+','Dword','guard0'),('div0','*','R0','Z0'),
    ('RA1','*','R1','portB'),('guard1','*','twice_H','K1'),
    ('rhs1','+','Dword','guard1'),('div1','*','R1','Z1')]


def source_check():
    parameters = ['q','F0','F1','F2','F3','R0','R1']
    auxiliaries = ['Hrep']+selector.CORE_NAMES+['portA','portB','K0','K1','Z0','Z1']
    z = {name:sp.Symbol(name) for name in parameters+auxiliaries}
    schedule = pairs.OUTER+selector.CORE+EXTRA
    env = selector.execute(schedule,z)
    equalities = [('q','q_calc'),('sum01','three_H'),('sum23','three_H'),('r','packed')]
    equalities += selector.kernel.EQUALITIES[1:]
    equalities += [('gate','F2'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]
    H,D = z['Hrep'],z['F0']-z['Hrep']
    sources = pairs.independent_sources(z)+[
        z['portA']+z['portB']+D-z['F2'],
        z['R0']*z['portA']-D-2*H*z['K0'],z['q']-z['R0']*z['Z0'],
        z['R1']*z['portB']-D-2*H*z['K1'],z['q']-z['R1']*z['Z1']]
    u = 2*z['r']+1+z['j']*z['c']
    correction = sources[11]*(u*u-z['y_aux']**2)
    records = []
    for index,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust = correction if index == 12 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0,index
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == 67 and counts['*'] == 36 and counts['+']+counts['-'] == 31
    assert len(equalities) == len(sources) == 19 and len(auxiliaries) == 24
    assert len(set(parameters+auxiliaries)) == len(parameters+auxiliaries)
    assert set().union(*(p.free_symbols for p in sources)) == set(z.values())
    return dict(operations=67,multiplications=36,additions_subtractions=31,equations=19,
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def word(bits):
    return sum(bit*3**j for j,bit in enumerate(bits))


def rotate(value,t,offset):
    q,R = 3**t,3**offset
    return value//R+(q//R)*(value%R)


def port_candidates():
    """Ports here range over arbitrary positive integers, not Boolean words."""
    checked = admitted = 0
    per_length = []
    for t in range(1,6):
        q,H = 3**t,(3**t-1)//2
        length_checked = length_admitted = 0
        for tail in product((0,1),repeat=t-1):
            digits = (1,)+tail
            D = word(digits)
            for v_digits in product((0,1),repeat=t):
                V = word(v_digits)
                port_sum = H+V-D
                for a,b in product(range(1,t+1),repeat=2):
                    R0,R1 = 3**a,3**b
                    expectedA,expectedB = rotate(D,t,a),rotate(D,t,b)
                    semantic_gate = all(x+y+z == 1+v for x,y,z,v in
                        zip(digits,digits[a:]+digits[:a],digits[b:]+digits[:b],v_digits))
                    for A in range(1,port_sum):
                        B = port_sum-A
                        num0,num1 = R0*A-D,R1*B-D
                        arithmetic = num0 > 0 and num1 > 0 and num0%(q-1) == num1%(q-1) == 0
                        semantic = A == expectedA and B == expectedB and semantic_gate
                        assert arithmetic == semantic,(t,D,V,a,b,A,B)
                        if arithmetic:
                            assert 0<A<q-1 and 0<B<q-1
                            length_admitted += 1
                        length_checked += 1
        checked += length_checked;admitted += length_admitted
        per_length.append(dict(t=t,candidates=length_checked,admitted=length_admitted))
    assert admitted > 0
    return dict(arbitrary_positive_port_tuples=checked,admitted=admitted,
                maximum_t=5,by_length=per_length)


def canonical_outer(digits,a,b):
    t = len(digits);q,H = 3**t,(3**t-1)//2
    ad,bd = digits[a:]+digits[:a],digits[b:]+digits[:b]
    sums = tuple(x+y+z for x,y,z in zip(digits,ad,bd))
    assert digits[0] == 1 and all(total in (1,2) for total in sums)
    vd = tuple(total-1 for total in sums)
    D,V,A,B = word(digits),word(vd),word(ad),word(bd)
    fields = (H+D,2*H-D,H+V,2*H-V)
    values = dict(q=q,Hrep=H,**{f'F{i}':F for i,F in enumerate(fields)},
                  R0=3**a,R1=3**b,portA=A,portB=B,K0=D%3**a,K1=D%3**b,
                  Z0=3**(t-a),Z1=3**(t-b))
    assert min(values.values()) > 0
    env = selector.execute(pairs.OUTER+EXTRA,values)
    for left,right in [('q','q_calc'),('sum01','three_H'),('sum23','three_H'),
                       ('gate','F2'),('RA0','rhs0'),('q','div0'),('RA1','rhs1'),('q','div1')]:
        assert env[left] == env[right]
    r = env['packed']
    assert r%2 == 0 and selector.valuation(r) == 4*t
    assert all(pairs.native(F,t) for F in fields) and fields[0]%3 == 2
    return dict(values=values,D=list(digits),A=list(ad),B=list(bd),V=list(vd),r=r,
                kernel_witnesses='Positive boolean_pairs56 converse; not materialized')


def direct_words():
    checked = admitted = zero_v = identity_ports = 0
    # This separate semantic scan uses bit sets, with no ternary congruence test.
    for t in range(1,13):
        mask = (1<<t)-1
        for tail in range(1<<(t-1)):
            d = 1+(tail<<1)
            for a,b in product(range(1,t+1),repeat=2):
                A = ((d>>a)|(d<<(t-a)))&mask
                B = ((d>>b)|(d<<(t-b)))&mask
                valid = (d|A|B) == mask and (d&A&B) == 0
                checked += 1
                if not valid:
                    continue
                admitted += 1
                majority = (d&A)|(d&B)|(A&B)
                assert all(((d>>j)&1)+((A>>j)&1)+((B>>j)&1) == 1+((majority>>j)&1)
                           for j in range(t))
                zero_v += majority == 0
                identity_ports += a == t or b == t
                # On moderate lengths, lift every admitted word to the actual
                # positive outer source, including its field packing valuation.
                if t <= 8:
                    canonical_outer(tuple((d>>j)&1 for j in range(t)),a,b)
    assert zero_v > 0 and identity_ports > 0
    return dict(boolean_word_offset_candidates=checked,admitted=admitted,
                maximum_t=12,outer_lift_maximum_t=8,zero_majority_words=zero_v,
                cases_with_identity_port=identity_ports)


def local_table():
    rows = []
    for d,A,B,V in product((0,1),repeat=4):
        relation = d+A+B == 1+V
        assert relation == (1 <= d+A+B <= 2 and V == int(d+A+B >= 2))
        if relation:
            rows.append([d,A,B,V])
    assert len(rows) == 6
    return rows


def verify():
    return dict(status='PASS_COMPLETE_CYCLIC_NAE_MAJORITY_67',source=source_check(),
                local_relation=local_table(),ports=port_candidates(),words=direct_words(),
                examples=[canonical_outer((1,0),1,1),canonical_outer((1,0,0),1,2),
                          canonical_outer((1,0),2,1)],
                dependencies={str(Path(module.__file__).name):hashlib.sha256(
                    Path(module.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for module in (pairs,selector,selector.kernel)},
                scope='Complete cyclic NAE/majority finite relation; no ordinary input, acceptance, or universal compiler',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result = verify();receipt = Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text()) == result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('source','dependencies')},indent=2))
