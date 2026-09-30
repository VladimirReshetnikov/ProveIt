"""Exact restricted72/71 noncommuting NAND relations; no universal claim."""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import sympy as sp
import native_controller_noncommuting73 as prior

selector = prior.selector


def source_check(mode):
    assert mode in (72, 71)
    unit_prefix = mode == 71
    auxiliaries = ['Hrep']+selector.CORE_NAMES+['C','E','Q','Jbound','portB','K0','K1','Z0','Z1']
    parameters = ['q','F0','F1','F2','R0','R1']
    if unit_prefix:
        auxiliaries.remove('K0')
    z = {name: sp.Symbol(name) for name in parameters+auxiliaries}
    extra = []
    for name, op, left, right in prior.EXTRA:
        if name == 'lhs0' or (unit_prefix and name == 'guard0'):
            continue
        if unit_prefix and name == 'rhs0':
            right = 'tail_modulus'
        extra.append((name, op, left, right))
    schedule = selector.OUTER54+selector.CORE+extra
    env = selector.execute(schedule, z)
    equalities = [('q','q_calc'),('sum012','four_H'),('r','packed')]+selector.kernel.EQUALITIES[1:]
    equalities += [('Eword','Dword'),('q','q_from_Q'),('Q','div0'),('boundQ','Q')]
    equalities += [('RA0','rhs0'),('ports','Sword'),('RA1','rhs1'),('q','div1')]
    H,F0,F2,q,Q,C,E = (z[name] for name in ('Hrep','F0','F2','q','Q','C','E'))
    R0 = z['R0']
    K0 = sp.Integer(1) if unit_prefix else z['K0']
    polynomials = selector.sources(z, True)
    polynomials += [3*E+1-2*H+F2, q-3*Q, Q-R0*z['Z0'],C+z['Jbound']-Q]
    polynomials += [R0*C-E-(Q-1)*K0, C+Q+z['portB']-H-F2+F0,
                    z['R1']*z['portB']-2*H+F2-2*H*z['K1'], q-z['R1']*z['Z1']]
    u = 2*z['r']+1+z['j']*z['c']
    correction = polynomials[10]*(u*u-z['y_aux']**2)
    records = []
    for index, ((left,right),source) in enumerate(zip(equalities,polynomials)):
        adjust = correction if index == 11 else 0
        assert sp.expand(env[left]-env[right]-source-adjust) == 0, (mode,index)
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),
                            correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in schedule)
    assert len(schedule) == mode
    assert counts['*'] == (37 if mode == 72 else 36)
    assert counts['+']+counts['-'] == 35
    assert len(equalities) == len(polynomials) == 21
    assert len(auxiliaries) == {72:27,71:26}[mode]
    assert len(set(parameters+auxiliaries)) == len(parameters+auxiliaries)
    assert set().union(*(p.free_symbols for p in polynomials)) == set(z.values())
    return dict(operations=mode,multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'],equations=len(equalities),
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records,
                prefix_condition='E mod R0 = 1' if unit_prefix else 'E mod R0 > 0')


def finite_candidates():
    checked = 0
    admitted = {72:0,71:0}
    for t in range(2,7):
        q,Q,H = 3**t,3**(t-1),(3**t-1)//2
        for tail in product(range(3), repeat=t-1):
            labels = (0,)+tail
            T = [sum(3**j for j,label in enumerate(labels) if label == i) for i in range(3)]
            D,S = H-T[2],H-T[0]+T[2]
            if D == 1:
                continue
            E = (D-1)//3
            for a,b in product(range(t),range(1,t+1)):
                R0,R1 = 3**a,3**b
                actualC,actualB = prior.rotate(E,t-1,a),prior.rotate(D,t,b)
                prefix = E % R0
                for C in range(1,Q):
                    B = S-C-Q
                    if B <= 0:
                        continue
                    n0,n1 = R0*C-E,R1*B-D
                    full = n1 > 0 and n1 % (q-1) == 0
                    arithmetic72 = full and n0 > 0 and n0 % (Q-1) == 0
                    arithmetic71 = full and n0 == Q-1
                    semantic = C == actualC and B == actualB
                    assert arithmetic72 == (semantic and prefix > 0)
                    assert arithmetic71 == (semantic and prefix == 1)
                    for mode,valid in ((72,arithmetic72),(71,arithmetic71)):
                        if valid:
                            admitted[mode] += 1
                            assert all(D//3**j%3 == 1-((C+Q)//3**j%3)*(B//3**j%3) for j in range(t))
                    checked += 1
    assert all(admitted.values())
    return dict(arbitrary_positive_port_tuples=checked,admitted={str(k):v for k,v in admitted.items()},maximum_t=6)


def common_positive_example():
    d,a,b = (1,1,0,0,1),1,3
    P = lambda x: x[1+a:]+x[1:1+a]+x[:1]
    Qrot = lambda x: x[b:]+x[:b]
    Aword,Bword = P(d),Qrot(d)
    assert d == tuple(1-x*y for x,y in zip(Aword,Bword))
    assert Aword[0] == Bword[0] == 0 and P(Qrot(d)) != Qrot(P(d))
    values = dict(q=243,Hrep=121,F0=122,F1=205,F2=157,R0=3,R1=27,
                  Dword=85,E=28,Q=81,C=36,Jbound=45,portA=117,portB=39,
                  K0=1,K1=4,Z0=27,Z1=9)
    assert values['F0']+values['F1']+values['F2'] == 4*values['Hrep']
    assert values['Dword'] == 2*values['Hrep']-values['F2'] == prior.word(d)
    assert values['portA'] == prior.word(Aword) and values['portB'] == prior.word(Bword)
    assert 3*values['E']+1 == values['Dword'] and values['q'] == 3*values['Q']
    assert values['R0']*values['Z0'] == values['Q']
    assert values['C']+values['Jbound'] == values['Q']
    assert values['R0']*values['C'] == values['E']+(values['Q']-1)*values['K0']
    assert values['portA'] == values['C']+values['Q']
    assert values['portA']+values['portB'] == values['Hrep']+values['F2']-values['F0']
    assert values['R1']*values['portB'] == values['Dword']+(values['q']-1)*values['K1']
    assert values['R1']*values['Z1'] == values['q']
    return dict(values=values,D=list(d),A=list(Aword),B=list(Bword),
                PQD=list(P(Qrot(d))),QPD=list(Qrot(P(d))),
                valid_modes=[72,71],kernel_witnesses='Positive selector converse; not materialized')


def omitted_bound_failures():
    # The previous73 missing-bound example still refutes unshifted72's
    # bound deletion, with K0 reduced by one.
    old = dict(q=243,Q=81,H=121,fields=[122,133,229],D=13,S=228,E=4,
               C=108,A=189,B=39,R0=3,R1=81,K0=4,K1=13,Z0=27,Z1=3)
    # Even K0=1 does not imply the bound while R0=1 remains possible.
    unit = dict(q=243,Q=81,H=121,fields=[122,157,205],D=37,S=204,E=12,
                C=92,A=173,B=31,R0=1,R1=9,K0=1,K1=1,Z0=81,Z1=27)
    for v in (old,unit):
        F0,F1,F2 = v['fields']
        assert F0+F1+F2 == 4*v['H'] and v['D'] == 2*v['H']-F2
        assert v['S'] == v['H']+F2-F0 and v['D'] == 3*v['E']+1
        assert v['q'] == 3*v['Q'] and v['Q'] == v['R0']*v['Z0']
        assert v['R0']*v['C'] == v['E']+(v['Q']-1)*v['K0']
        assert v['A'] == v['C']+v['Q'] and v['A']+v['B'] == v['S']
        assert v['R1']*v['B'] == v['D']+(v['q']-1)*v['K1']
        assert v['q'] == v['R1']*v['Z1'] and v['C'] >= v['Q']
        assert any(v['A']//3**j%3 == 2 for j in range(5))
    return dict(unshifted_unbounded=old,unit_prefix_unbounded=unit,
                scope='These delete the retained bound; neither is one of the proved72/71 sources')


def rotate_bits(value, length, amount):
    amount %= length
    return ((value >> amount) | (value << (length-amount))) & ((1 << length)-1)


def uniform_prefix_structure():
    """Direct Boolean semantics beyond the arithmetic tuple enumeration."""
    candidates = admitted = 0
    distances = Counter()
    for t in range(2,18):
        mask = (1 << t)-1
        for a in range(1,t):
            # Exactly E mod 3^a=1: d0=d1=1 and d2...da=0.
            # d_(a+1) remains free, so initial port typing is checked.
            for high in range(1 << (t-a-1)):
                d = 3 | (high << (a+1))
                pd = rotate_bits(d >> 1,t-1,a) | (1 << (t-1))
                for b in range(1,t+1):
                    candidates += 1
                    qd = rotate_bits(d,t,b)
                    if pd & 1 or qd & 1 or d != mask ^ (pd & qd):
                        continue
                    admitted += 1
                    assert a <= t-2
                    assert all((d >> j) & 1 == 0 for j in range(2,a+2))
                    assert all((qd >> j) & 1 == 1 for j in range(2,a+1))
                    s = a+1
                    rd = rotate_bits(d,t,s)
                    pqd = rotate_bits(qd >> 1,t-1,a) | ((qd & 1) << (t-1))
                    target = rotate_bits(qd,t,s)
                    first_error = (pd ^ rd).bit_count()
                    second_error = (pqd ^ target).bit_count()
                    distance = (d ^ target).bit_count()
                    assert first_error <= 2 and second_error <= 2
                    assert distance <= first_error+second_error <= 4
                    distances[distance] += 1
    # A full semantic71 point attains4, so the uniform numerical bound is sharp.
    digits = (1,1,0,0,1,1,1,0)
    t,a,b = 8,2,2
    p_digits = digits[1+a:]+digits[1:1+a]+digits[:1]
    q_digits = digits[b:]+digits[:b]
    target_digits = digits[a+b+1:]+digits[:a+b+1]
    assert digits == tuple(1-x*y for x,y in zip(p_digits,q_digits))
    assert p_digits[0] == q_digits[0] == 0
    E = (prior.word(digits)-1)//3
    assert E % 3**a == 1
    assert sum(x != y for x,y in zip(digits,target_digits)) == 4
    assert distances[4] > 0
    return dict(prefix_word_offset_candidates=candidates,admitted=admitted,
                maximum_t=17,distance_counts={str(k):v for k,v in sorted(distances.items())},
                sharp_example=dict(t=t,a=a,b=b,D=list(digits),A=list(p_digits),B=list(q_digits),
                                   composed_rotation=list(target_digits),hamming_distance=4),
                scope='Direct71 semantics and sharpness of the proved uniform bound; not a decidability test')


def free_block_family():
    checked = 0
    for k in range(9):
        t = 10*k+5
        seen = set()
        for bits in product((0,1),repeat=k):
            U = tuple(x for bit in bits for x in ((0,1,0,1,1) if bit == 0 else (0,1,1,0,1)))
            w = (1,)+U+(0,1,1,0)+(1,1,0,1,0)*k
            assert len(w) == t
            assert all(w[j] == 1-w[(j-1)%t]*w[(j+1)%t] for j in range(t))
            d = [0]*t
            for j,value in enumerate(w):
                d[2*j%t] = value
            d = tuple(d)
            assert d not in seen
            seen.add(d)
            P = lambda row: row[2:]+row[1:2]+row[:1]
            Qrot = lambda row: row[-2:]+row[:-2]
            Aword,Bword = P(d),Qrot(d)
            assert d[0] == d[1] == d[-1] == 1 and d[2] == d[-2] == 0
            assert d == tuple(1-x*y for x,y in zip(Aword,Bword))
            assert Aword[0] == Bword[0] == 0
            assert Qrot(P(d)) == d and P(Qrot(d)) != d
            q,Q,H = 3**t,3**(t-1),(3**t-1)//2
            D,A,B = prior.word(d),prior.word(Aword),prior.word(Bword)
            E,C = (D-1)//3,A-Q
            R0,R1 = 3,3**(t-2)
            K1 = D % R1
            labels = tuple(x+y for x,y in zip(Aword,Bword))
            fields = [H+sum(3**j for j,label in enumerate(labels) if label == i) for i in range(3)]
            assert sum(fields) == 4*H and fields[0] % 3 == 2
            assert D == 2*H-fields[2] and A+B == H+fields[2]-fields[0]
            assert E % R0 == 1 and R0*C == E+Q-1
            assert R1*B == D+(q-1)*K1
            assert min(E,C,Q-C,B,K1,Q//R0,q//R1) > 0
            checked += 1
        assert len(seen) == 2**k
    return dict(checked=checked,maximum_free_bits=8,maximum_word_length=85,
                family='2^k noncommuting71 semantic points at t=10k+5, a=1, b=t-2',
                scope='A regular block family with explicit positive outer witnesses; not universality')


def verify():
    return dict(status='PASS_RESTRICTED_NONCOMMUTING_72_71',
                sources={str(mode):source_check(mode) for mode in (72,71)},
                finite=finite_candidates(),positive_example=common_positive_example(),
                omitted_bound_failures=omitted_bound_failures(),
                uniform_prefix_structure=uniform_prefix_structure(),
                free_block_family=free_block_family(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
                established_complete_bound=76,
                scope='Complete finite relations on progressively narrower permutation classes; no universal compiler or raw-input initialization')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if parser.parse_args().write:
        receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print(result['finite'])
    print(result['uniform_prefix_structure'])
    print(result['free_block_family'])
