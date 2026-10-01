#!/usr/bin/env python3
"""Seven-dimensional scalar-zero lift and rank-one mortality adapter.

Finite checks do not instantiate the universal subgroup or pay for an
arbitrary selected word. The note gives those precise scope boundaries.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random


I2 = ((1, 0), (0, 1))
ROTATION = ((0, -1), (1, 0))
ROW = (1, 0, 1, 1, 0, 1, -4)


def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def mv(a, v):
    return tuple(sum(x*y for x, y in zip(row, v)) for row in a)


def dot(u, v):
    return sum(a*b for a, b in zip(u, v))


def transpose(a):
    return tuple(zip(*a))


def inv(a):
    p, q = a[0]
    s, t = a[1]
    assert p*t-q*s == 1
    return ((t, -q), (-s, p))


def ident(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def sym(a):
    """Action on (g11,-g12,g22), so G -> a G a^T."""
    p, q = a[0]
    s, t = a[1]
    return ((p*p, -2*p*q, q*q),
            (-p*s, p*t+q*s, -q*t),
            (s*s, -2*s*t, t*t))


def lift(pair):
    blocks = (sym(pair[0]), sym(pair[1]), ((1,),))
    result = [[0]*7 for _ in range(7)]
    offset = 0
    for block in blocks:
        for i, row in enumerate(block):
            for j, value in enumerate(row):
                result[offset+i][offset+j] = value
        offset += len(block)
    return tuple(map(tuple, result))


def target(r):
    return ((1+r, 1), (-r*r, 1-r))


def gram(r):
    h, t, z = r-1, r+1, r*r
    return (h*h+1, h*z+t, z*z+t*t)


def column(r):
    a, b, c = gram(r)
    return (a, b, c, a, b, c, 1)


def sentinel(r):
    return tuple(tuple(a*b for b in ROW) for a in column(r))


def scalar(pair, r):
    return dot(ROW, mv(lift(pair), column(r)))


def loader(alpha=24, beta=12, rank_one=False):
    assert alpha > 0 and beta > 0
    source = [
        ('scaled', '*', alpha, 'x'), ('r', '+', 'scaled', beta),
        ('h', '-', 'r', 1), ('t', '+', 'r', 1),
        ('z', '*', 'r', 'r'), ('hh', '*', 'h', 'h'),
        ('a', '+', 'hh', 1), ('hz', '*', 'h', 'z'),
        ('b', '+', 'hz', 't'), ('zz', '*', 'z', 'z'),
        ('tt', '*', 't', 't'), ('c', '+', 'zz', 'tt')]
    if rank_one:
        source += [(f'minus4_{name}', '*', -4, name) for name in ('a', 'b', 'c')]
    return source


def nonnegative_loader(alpha=24, beta=12):
    assert alpha > 0 and beta > 0
    return [
        ('scaled', '*', alpha, 'x'), ('r', '+', 'scaled', beta),
        ('h', '-', 'r', 1), ('z', '*', 'r', 'r'),
        ('u', '+', 'z', 1), ('hh', '*', 'h', 'h'),
        ('a', '+', 'hh', 1), ('hu', '*', 'h', 'u'),
        ('b', '+', 'hu', 2), ('v', '*', 'u', 'u'),
        ('c_partial', '-', 'v', 'a'), ('c', '+', 'c_partial', 2),
        ('input_head', '+', 'v', 'v')]


def basis_change():
    P = list(ident(7))
    Pinv = list(ident(7))
    P[0] = ROW
    Pinv[0] = tuple(2*int(j == 0)-v for j, v in enumerate(ROW))
    return tuple(P), tuple(Pinv)


def boolean_matrix(a):
    return tuple(tuple(int(x != 0) for x in row) for row in a)


def boolean_product(a, b):
    return boolean_matrix(mm(a, b))


def support_mortal(alphabet):
    reached = set()
    frontier = list(alphabet)
    while frontier:
        value = frontier.pop()
        if value in reached:
            continue
        reached.add(value)
        if not any(any(row) for row in value):
            return True
        frontier.extend(boolean_product(value, a) for a in alphabet)
    return False


def execute(source, values):
    env = dict(values)
    for name, op, left, right in source:
        assert name not in env
        a = left if isinstance(left, int) else env[left]
        b = right if isinstance(right, int) else env[right]
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def counts(source):
    result = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(M=result['M'], A=result['A'], operations=len(source))


def shear(axis, sign):
    assert axis in ('upper', 'lower') and sign in (-1, 1)
    return ((1, sign), (0, 1)) if axis == 'upper' else ((1, 0), (sign, 1))


def signed_step(state, axis, sign):
    a, b, c = state
    if axis == 'upper':
        following = b-sign*c
        return (a-sign*b-sign*following, following, c)
    following = b-sign*a
    return (a, following, c-sign*b-sign*following)


def build_fixed_word(word, alpha=24, beta=12):
    """word is a FIXED sequence (block,axis,sign), never a free witness."""
    source = loader(alpha, beta)
    source += [('two_D', '+', 'D', 'D'), ('initial_bhat', '+', 'b', 'D')]
    state = [['a', 'initial_bhat', 'c'], ['a', 'initial_bhat', 'c']]
    comparisons, auxiliaries = [], ['D']
    for k, (block, axis, sign) in enumerate(word):
        assert block in (0, 1) and axis in ('upper', 'lower') and sign in (-1, 1)
        old = state[block]
        changing, fixed = (0, 2) if axis == 'upper' else (2, 0)
        bhat, diagonal = f'B{k}', f'A{k}'
        auxiliaries += [bhat, diagonal]
        source.append((f'next_b{k}', '-' if sign == 1 else '+', old[1], old[fixed]))
        source.append((f'first{k}', '-' if sign == 1 else '+', old[changing], old[1]))
        source.append((f'second{k}', '-' if sign == 1 else '+', f'first{k}', bhat))
        source.append((f'next_diag{k}', '+' if sign == 1 else '-', f'second{k}', 'two_D'))
        comparisons += [(f'next_b{k}', bhat), (f'next_diag{k}', diagonal)]
        state[block][1], state[block][changing] = bhat, diagonal
    source += [('trace0', '+', state[0][0], state[0][2]),
               ('trace1', '+', state[1][0], state[1][2]),
               ('endpoint', '+', 'trace0', 'trace1')]
    comparisons.append(('endpoint', 4))
    return dict(source=source, comparisons=comparisons, auxiliaries=auxiliaries,
                word=word, alpha=alpha, beta=beta)


def residuals(packet, env):
    def get(z):
        return z if isinstance(z, int) else env[z]
    return [get(a)-get(b) for a, b in packet['comparisons']]


def polynomial_source(packet):
    source = list(packet['source'])
    squares = []
    for k, (left, right) in enumerate(packet['comparisons']):
        source += [(f'residual{k}', '-', left, right),
                   (f'square{k}', '*', f'residual{k}', f'residual{k}')]
        squares.append(f'square{k}')
    total = squares[0]
    for k, square in enumerate(squares[1:]):
        name = f'total{k}'
        source.append((name, '+', total, square))
        total = name
    return source, total


def fixture(packet, x):
    r = packet['alpha']*x+packet['beta']
    state = [gram(r), gram(r)]
    history = []
    for block, axis, sign in packet['word']:
        state[block] = signed_step(state[block], axis, sign)
        history.append((block, axis, state[block]))
    D = 1+max([abs(gram(r)[1])]+[abs(s[1]) for _, _, s in history])
    result = dict(x=x, D=D)
    for k, (_, axis, s) in enumerate(history):
        result[f'B{k}'] = s[1]+D
        result[f'A{k}'] = s[0 if axis == 'upper' else 2]
    assert all(v > 0 for v in result.values())
    return result


def direct_pair(word):
    pair = [I2, I2]
    for block, axis, sign in word:
        pair[block] = mm(shear(axis, sign), pair[block])
    return tuple(pair)


def run_checks():
    rng = random.Random(730921)
    assert counts(loader()) == dict(M=6, A=6, operations=12)
    assert counts(loader(rank_one=True)) == dict(M=9, A=6, operations=15)
    assert counts(nonnegative_loader()) == dict(M=5, A=8, operations=13)
    P, Pinv = basis_change()
    assert mm(P, Pinv) == mm(Pinv, P) == ident(7)
    loader_cases = 0
    for alpha, beta, x in product((1, 12, 24, 120), (1, 12, 36), range(1, 33)):
        z = execute(loader(alpha, beta, True), {'x': x})
        r = alpha*x+beta
        a, b, c = gram(r)
        assert (z['a'], z['b'], z['c']) == (a, b, c)
        assert min(a, b, c) > 0 and a*c-b*b == 1
        G = mm(inv(target(r)), transpose(inv(target(r))))
        assert G == ((a, -b), (-b, c))
        assert tuple(z[f'minus4_{n}'] for n in ('a', 'b', 'c')) == (-4*a, -4*b, -4*c)
        positive_z = execute(nonnegative_loader(alpha, beta), {'x': x})
        transformed = mv(P, column(r))
        assert transformed == (positive_z['input_head'], b, c, a, b, c, 1)
        assert transformed[0] == 2*(r*r+1)**2 and min(transformed) > 0
        expected = tuple((v, 0, 0, 0, 0, 0, 0) for v in transformed)
        assert mm(mm(P, sentinel(r)), Pinv) == expected
        loader_cases += 1

    small = [((a, b), (c, d)) for a, b, c, d in product(range(-3, 4), repeat=4)
             if a*d-b*c == 1]
    rotations = {I2, ROTATION, ((-1, 0), (0, -1)), ((0, 1), (-1, 0))}
    for matrix in small:
        norm = sum(v*v for row in matrix for v in row)
        assert norm >= 2 and (norm == 2) == (matrix in rotations)
    representation_cases = 0
    for _ in range(512):
        left, right = rng.choice(small), rng.choice(small)
        assert mm(sym(left), sym(right)) == sym(mm(left, right))
        r = rng.randrange(1, 41)
        pair = (left, right)
        norm = sum(v*v for block in pair for row in mm(block, inv(target(r))) for v in row)-4
        assert scalar(pair, r) == norm >= 0
        changed = mm(mm(P, lift(pair)), Pinv)
        assert mv(changed, mv(P, column(r)))[0] == norm
        for axis, sign in product(('upper', 'lower'), (-1, 1)):
            state = tuple(rng.randrange(-50, 51) for _ in range(3))
            assert signed_step(state, axis, sign) == mv(sym(shear(axis, sign)), state)
        representation_cases += 1

    # Torsion really must be excluded by the fixed macro group.
    r = 12
    false_pair = (mm(ROTATION, target(r)), target(r))
    assert scalar(false_pair, r) == 0 and false_pair != (target(r), target(r))

    # Exact sentinel factorization, with arbitrarily many separators.
    mortality_cases = zero_cases = 0
    zero7 = tuple((0,)*7 for _ in range(7))
    for trial in range(256):
        r = rng.randrange(1, 12)
        segments = [(rng.choice(small), rng.choice(small)) for _ in range(rng.randrange(2, 6))]
        if trial % 2 == 0 and len(segments) > 2:
            segments[rng.randrange(1, len(segments)-1)] = (target(r), target(r))
        # Guarantee the intentionally zero family has an internal target segment.
        if trial % 2 == 0 and len(segments) == 2:
            segments.insert(1, (target(r), target(r)))
        R = sentinel(r)
        dense = lift(segments[0])
        for segment in segments[1:]:
            dense = mm(mm(dense, R), lift(segment))
        internal = [scalar(pair, r) for pair in segments[1:-1]]
        answer = any(value == 0 for value in internal)
        assert (dense == zero7) == answer
        factor = 1
        for value in internal:
            factor *= value
        outer = mm(mm(lift(segments[0]), R), lift(segments[-1]))
        assert dense == tuple(tuple(factor*x for x in row) for row in outer)
        mortality_cases += 1
        zero_cases += answer
    assert zero_cases > 0

    # Finite support closure is an exact mortality decision for nonnegative
    # matrices, independent of positive entry magnitudes.
    support_cases = 0
    for _ in range(128):
        base = [tuple(tuple(rng.randrange(2) for _ in range(2)) for _ in range(2))
                for _ in range(2)]
        sentinel_support = ((1, 0), (1, 0))
        expected = support_mortal(base+[sentinel_support])
        for magnitude in (1, 3, 17):
            weighted = [tuple(tuple(x*rng.randrange(1, 20) for x in row) for row in a)
                        for a in base]
            weighted.append(((magnitude, 0), (magnitude+1, 0)))
            assert support_mortal([boolean_matrix(a) for a in weighted]) == expected
            dense = ident(2)
            support = ident(2)
            for _ in range(12):
                a = rng.choice(weighted)
                dense = mm(dense, a)
                support = boolean_product(support, boolean_matrix(a))
                assert boolean_matrix(dense) == support
            support_cases += 1

    fixed_word_cases = arbitrary_residual_cases = accepted = 0
    for trial in range(256):
        word = [(rng.randrange(2), rng.choice(('upper', 'lower')), rng.choice((-1, 1)))
                for _ in range(rng.randrange(0, 17))]
        packet = build_fixed_word(word)
        t = len(word)
        assert len(packet['auxiliaries']) == 2*t+1
        assert len(packet['comparisons']) == 2*t+1
        assert counts(packet['source']) == dict(M=6, A=4*t+11, operations=4*t+17)
        sos, output = polynomial_source(packet)
        assert counts(sos) == dict(M=2*t+7, A=8*t+12, operations=10*t+19)
        x = rng.randrange(1, 12)
        z = fixture(packet, x)
        env = execute(packet['source'], z)
        actual = residuals(packet, env)
        assert not any(actual[:-1])
        assert actual[-1] == scalar(direct_pair(word), 24*x+12)
        assert execute(sos, z)[output] == sum(v*v for v in actual)
        fixed_word_cases += 1
        # Independently form all positive shifted residuals off the zero set.
        z = {key: rng.randrange(1, 100) for key in ['x']+packet['auxiliaries']}
        initial = gram(24*z['x']+12)
        state = [initial, initial]
        manual = []
        for k, (block, axis, sign) in enumerate(word):
            a, b, c = state[block]
            next_b = z[f'B{k}']-z['D']
            next_diag = z[f'A{k}']
            expected_b = b-sign*(c if axis == 'upper' else a)
            expected_diag = (a if axis == 'upper' else c)-sign*b-sign*next_b
            manual += [expected_b-next_b, expected_diag-next_diag]
            state[block] = ((next_diag, next_b, c) if axis == 'upper'
                            else (a, next_b, next_diag))
        manual.append(sum(s[0]+s[2] for s in state)-4)
        actual = residuals(packet, execute(packet['source'], z))
        assert actual == manual
        assert execute(sos, z)[output] == sum(v*v for v in manual)
        # The total degree bound is proved from linearity after loading.
        # This independently verifies an exact nonzero degree-eight x slice.
        evaluations = [execute(sos, dict(z, x=j))[output] for j in range(10)]
        for _ in range(8):
            evaluations = [b-a for a, b in zip(evaluations, evaluations[1:])]
        assert evaluations[0] == evaluations[1] > 0
        arbitrary_residual_cases += 1

    for x in range(1, 5):
        r = 24*x+12
        word = []
        for block in (0, 1):
            word += [(block, 'lower', 1)]*r+[(block, 'upper', 1)]+[(block, 'lower', -1)]*r
        packet = build_fixed_word(word)
        z = fixture(packet, x)
        assert direct_pair(word) == (target(r), target(r))
        assert not any(residuals(packet, execute(packet['source'], z)))
        # The same fixed word rejects a different ordinary input.
        wrong = fixture(packet, x+1)
        assert residuals(packet, execute(packet['source'], wrong))[-1] > 0
        z['A0'] += 1
        assert any(residuals(packet, execute(packet['source'], z)))
        accepted += 1

    return dict(status='PASS', scalar_dimension=7, loader=counts(loader()),
                rank_one_loader=counts(loader(rank_one=True)),
                nonnegative_rank_one_loader=counts(nonnegative_loader()),
                fixed_word_graph='6M+(4t+11)A = 4t+17',
                fixed_word_polynomial='(2t+7)M+(8t+12)A = 10t+19',
                fixed_word_positive_witnesses='2t+1', fixed_word_equations='2t+1',
                fixed_word_polynomial_degree=8,
                loader_cases=loader_cases, determinant_one_small_matrices=len(small),
                representation_cases=representation_cases,
                signed_shear_identity_cases=4*representation_cases,
                sentinel_factorization_cases=mortality_cases,
                zero_sentinel_cases=zero_cases, fixed_word_cases=fixed_word_cases,
                nonnegative_support_cases=support_cases,
                arbitrary_positive_residual_cases=arbitrary_residual_cases,
                accepted_fixed_words_and_wrong_input_tests=accepted,
                torsion_counterexample=True,
                boundary='Universal generators are inherited abstractly, not transcribed. '
                         'No variable-word or regular-controller cost is included.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = run_checks()
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == result
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
