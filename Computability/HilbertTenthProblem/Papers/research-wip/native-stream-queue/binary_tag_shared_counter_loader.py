"""Paid fixed-block boundary with a counter sharing the recoder scale.

This is a boundary component, conditional on typed Q and z. It does not
assert a complete ordinary-input universal tag polynomial.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random


def execute(source, values):
    env = dict(values)
    get = lambda x: env[x] if isinstance(x, str) else x
    for name, op, a, b in source:
        assert name not in env
        a, b = get(a), get(b)
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def word_value(word):
    assert all(c in '01' for c in word)
    return int(word or '0', 2)


def constants(prefix, data0, data1, middle, mu, tail):
    D, t = len(data0), len(mu)
    assert D >= 2 and t >= 1 and D % t == 0 and len(data1) == D
    p = (1 << len(prefix)) + word_value(prefix)
    v0, v1, b, M, e = map(word_value, (data0, data1, middle, mu, tail))
    f, g, L = len(middle), len(tail), (1 << D)-1
    Cmu = L // ((1 << t)-1)
    assert Cmu*((1 << t)-1) == L
    A = (1 << (f+g))*(p*L+v0)
    B = (1 << (f+g))*(v1-v0)
    T = (1 << g)*(((1 << f)*p+b)*L+M*Cmu)
    E = (1 << g)*((1 << f)*p+b)+e
    assert min(A, T, E) > 0
    return dict(prefix=prefix, data0=data0, data1=data1, middle=middle,
                mu=mu, tail=tail, D=D, t=t, m=D//t, p=p, v0=v0, v1=v1,
                b=b, M=M, e=e, f=f, g=g, L=L, Cmu=Cmu, A=A, B=B, T=T, E=E)


def build(c, shared_modulus=False, supplied_output=False):
    """Shared mode requires modulus to be the existing literal Q-1 register."""
    source = [] if shared_modulus else [('modulus', '-', 'Q', 1)]
    source += [
        ('repunit_product', '*', c['L'], 'r'),
        ('prefix_data', '*', c['A'], 'r'),
        ('data_delta', '*', c['B'], 'z'),
        ('data_body', '+', 'prefix_data', 'data_delta'),
        ('data_counter_scale', '*', 'data_body', 'Q'),
        ('counter_frame', '*', c['T'], 'r'),
        ('before_tail', '+', 'data_counter_scale', 'counter_frame'),
        ('tag_input', '+', 'before_tail', c['E'])]
    pairs = [('repunit_product', 'modulus')]
    parameters = ['Q', 'z'] + (['modulus'] if shared_modulus else [])
    if supplied_output:
        parameters += ['tag_value']
        pairs += [('tag_input', 'tag_value')]
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': 5, 'A': 3 if shared_modulus else 4}
    return dict(source=source, comparisons=pairs, parameters=parameters,
                auxiliaries=['r'], output='tag_input', operations=len(source),
                multiplications=counts['M'], additions_subtractions=counts['A'],
                equations=len(pairs), witnesses=1, shared_modulus=shared_modulus,
                supplied_output=supplied_output, constants=c)


def direct(c, Q, z, r):
    data = c['p']*Q+c['v0']*r+(c['v1']-c['v0'])*z
    framed = data*(1 << c['f'])+c['b']
    return (framed*Q+c['M']*c['Cmu']*r)*(1 << c['g'])+c['e']


def folded(c, Q, z, r):
    return (c['A']*r+c['B']*z)*Q+c['T']*r+c['E']


def spread(x, D):
    return sum(((x >> j) & 1) << (D*j) for j in range(x.bit_length()))


def frame(c, bits):
    return (c['prefix']+''.join(c['data1'] if bit == '1' else c['data0'] for bit in bits)
            +c['middle']+c['mu']*(c['m']*len(bits))+c['tail'])


def ledger(packet):
    return {key: packet[key] for key in ('operations', 'multiplications',
            'additions_subtractions', 'equations', 'witnesses',
            'shared_modulus', 'supplied_output')}


def verify():
    rng = random.Random(8051968)
    identities = signed = frames = nonpowers = positive_definitions = 0
    records = []
    for D, t in ((2, 1), (4, 1), (6, 2), (8, 1), (8, 4), (12, 3), (16, 2), (24, 3)):
        for order in (-1, 0, 1):
            low = rng.randrange(1 << D)
            high = rng.randrange(low, 1 << D)
            if order and high == low:
                low, high = 0, (1 << D)-1
            v0, v1 = (low, high) if order == 1 else (high, low) if order == -1 else (low, low)
            bits = lambda value, width: format(value, f'0{width}b')
            c = constants('101', bits(v0, D), bits(v1, D), '001',
                          bits(rng.randrange(1 << t), t), '1001')
            p = build(c)
            for case in range(32):
                Q, z, r = [rng.randrange(1, 25) if case < 16 else rng.randrange(-12, 13) for _ in range(3)]
                env = execute(p['source'], dict(Q=Q, z=z, r=r))
                assert env['tag_input'] == folded(c, Q, z, r)
                correction = ((1 << c['g'])*((1 << c['f'])*c['p']*(Q+1)+c['b'])
                              *(Q-c['L']*r-1))
                assert direct(c, Q, z, r)-env['tag_input'] == correction
                identities += 1
                signed += case >= 16
                if order >= 0 and min(Q, z, r) > 0:
                    assert env['tag_input'] > 0
                    positive_definitions += 1
            for n in range(1, 13):
                for x in sorted({1, (1 << n)-1, rng.randrange(1, 1 << n)}):
                    Q = 1 << (D*n)
                    z, r = spread(x, D), (Q-1)//c['L']
                    env = execute(p['source'], dict(Q=Q, z=z, r=r))
                    word = frame(c, format(x, f'0{n}b'))
                    actual = (1 << len(word))+word_value(word)
                    assert env['repunit_product'] == env['modulus']
                    assert env['tag_input'] == direct(c, Q, z, r) == actual > 0
                    assert c['Cmu']*r == (Q-1)//((1 << t)-1)
                    frames += 1
                    nonpowers += bool(n & (n-1))
            records.append(dict(D=D, t=t, block_value_order=order, **ledger(p)))
    # Degree is literal in independent Q,z,r, without using Q=Lr+1.
    c = constants('101', '0010', '0111', '00', '10', '101')
    packet = build(c)
    degrees = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    for name, op, a, b in packet['source']:
        da = degrees[a] if isinstance(a, str) else 0
        db = degrees[b] if isinstance(b, str) else 0
        degrees[name] = da+db if op == '*' else max(da, db)
    assert degrees['tag_input'] == 2 and c['A'] > 0
    # Empty fixed frames, zero counter word and either data ordering are allowed.
    edges = []
    for v0, v1 in ((0, 3), (3, 0), (1, 1)):
        edge = constants('', format(v0, '02b'), format(v1, '02b'), '', '0', '')
        for n in range(1, 5):
            x = (1 << n)-1
            Q = 1 << (2*n)
            r = (Q-1)//3
            assert folded(edge, Q, spread(x, 2), r) == int('1'+frame(edge, format(x, f'0{n}b')), 2)
        edges.append(dict(v0=v0, v1=v1))
    return dict(status='PASS_BINARY_TAG_SHARED_COUNTER_LOADER',
                variant_ledgers=records,
                interface_ledgers=[ledger(build(c, shared, supplied))
                                   for shared in (False, True) for supplied in (False, True)],
                example=build(c, True), complete_correction_identities=identities,
                signed_cases=signed, literal_binary_frames=frames,
                non_dyadic_duration_frames=nonpowers,
                positive_off_zero_definitions=positive_definitions,
                degenerate_fixed_word_cases=edges, exact_boundary_output_degree=2,
                scope='Paid fixed-block boundary, conditional on typed recoder Q,z and '
                      'counter exponent m*n. Shared mode requires an actual Q-1 register. '
                      'Dyadic duration, machine normalization and history remain separate; '
                      'no complete ordinary-input universal operation count is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['interface_ledgers'])
