#!/usr/bin/env python3
"""Linear projective universal input; a six-dimensional three-gate sentinel.

The universal finite presentation is not instantiated. Finite group fixtures
check exact witnesses and rejection invariants, not bounded universality.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import group_commutator_universal_substrate as free
import group_gram_zero_mortality as gram


I = gram.I2
U = ((1, 1), (0, 1))
V = ((1, 0), (4, 1))
B = ((1, 0), (12, 1))
ROW = (1, 0, 0, 1, 0, 0)


def power(matrix, exponent):
    if exponent < 0:
        matrix, exponent = gram.inv(matrix), -exponent
    value = I
    while exponent:
        if exponent & 1:
            value = gram.mm(value, matrix)
        matrix = gram.mm(matrix, matrix)
        exponent //= 2
    return value


def matrix_word(word, images):
    value = I
    for letter in word:
        matrix = images[abs(letter)]
        value = gram.mm(value, matrix if letter > 0 else gram.inv(matrix))
    return value


def target(r):
    return gram.target(r)


def vector_at_input(x, alpha=24, beta=12):
    return (-1, alpha*x+beta+1)


def loader(alpha=24, beta=12):
    assert alpha > 0 and beta > 0
    return [('scaled', '*', alpha, 'x'), ('input_t', '+', 'scaled', beta+1),
            ('input_t2', '*', 'input_t', 'input_t')]


def column(t):
    return (1, t, t*t, 1, t, t*t)


def lift(pair):
    result = [[0]*6 for _ in range(6)]
    for block, A in enumerate(pair):
        for i, row in enumerate(gram.sym(A)):
            for j, value in enumerate(row):
                result[3*block+i][3*block+j] = value
    return tuple(map(tuple, result))


def scalar(pair, t):
    return gram.dot(ROW, gram.mv(lift(pair), column(t)))


def sentinel(t):
    return tuple(tuple(v*u for u in ROW) for v in column(t))


def stabilizer_power(P, r):
    """For tested P,L in Gamma, return n iff P=B^n L."""
    value = gram.mm(P, gram.inv(target(r)))
    if value[0][1] != 0:
        return None
    assert value[0][0] == value[1][1] == 1
    assert value[1][0] % 12 == 0
    return value[1][0]//12


def build_fixed_word(word, alpha=24, beta=12):
    source = loader(alpha, beta)+[
        ('two_D', '+', 'D', 'D'),
        ('initial_bhat', '+', 'input_t', 'D'),
        ('initial_chat', '+', 'input_t2', 1)]
    states = [[2, 'initial_bhat', 'initial_chat'], [2, 'initial_bhat', 'initial_chat']]
    comparisons, auxiliaries = [], ['D']
    for k, (block, axis, sign) in enumerate(word):
        assert block in (0, 1) and axis in ('upper', 'lower') and sign in (-1, 1)
        state = states[block]
        changing, fixed = (0, 2) if axis == 'upper' else (2, 0)
        bhat, diagonal = f'B{k}', f'A{k}'
        auxiliaries += [bhat, diagonal]
        source += [
            (f'btemp{k}', '-' if sign == 1 else '+', state[1], state[fixed]),
            (f'next_b{k}', '+' if sign == 1 else '-', f'btemp{k}', 1),
            (f'dfirst{k}', '-' if sign == 1 else '+', state[changing], state[1]),
            (f'dsecond{k}', '-' if sign == 1 else '+', f'dfirst{k}', bhat),
            (f'next_diag{k}', '+' if sign == 1 else '-', f'dsecond{k}', 'two_D')]
        comparisons += [(f'next_b{k}', bhat), (f'next_diag{k}', diagonal)]
        states[block][1], states[block][changing] = bhat, diagonal
    source.append(('endpoint', '+', states[0][0], states[1][0]))
    comparisons.append(('endpoint', 2))
    return dict(source=source, comparisons=comparisons, auxiliaries=auxiliaries,
                word=word, alpha=alpha, beta=beta)


def fixture(packet, x):
    t = packet['alpha']*x+packet['beta']+1
    states = [(1, t, t*t), (1, t, t*t)]
    history = []
    for block, axis, sign in packet['word']:
        states[block] = gram.signed_step(states[block], axis, sign)
        history.append((axis, states[block]))
    D = 1+max([abs(t)]+[abs(state[1]) for _, state in history])
    result = dict(x=x, D=D)
    for k, (axis, state) in enumerate(history):
        result[f'B{k}'] = state[1]+D
        result[f'A{k}'] = state[0 if axis == 'upper' else 2]+1
    assert min(result.values()) > 0
    return result


def graph_abelianization(vertices):
    result = Counter()
    for i, sign in vertices:
        result[i] += sign
    return {i: v for i, v in result.items() if v}


def group_checks():
    images = {1: U, 2: B,
              3: gram.mm(gram.mm(V, U), gram.inv(V)),
              4: gram.mm(gram.mm(power(V, 2), U), power(V, -2))}
    base = {1: U, 2: V}
    # Schreier words in the ambient free group on U,V.
    schreier = {1: (1,), 2: (2, 2, 2), 3: (2, 1, -2), 4: (2, 2, 1, -2, -2)}
    for i in images:
        assert matrix_word(schreier[i], base) == images[i]
    kernel_cases = 0
    for word in free.reduced_words(2, 7):
        exp_v = sum(1 if c == 2 else -1 if c == -2 else 0 for c in word)
        matrix = matrix_word(word, base)
        assert matrix[0][0] % 4 == matrix[1][1] % 4 == 1
        assert matrix[1][0] % 4 == 0
        if matrix[0][1] == 0:
            assert matrix[0][0] == matrix[1][1] == 1
            n = matrix[1][0]//4
            assert word == free.power((2,), n)
            assert (exp_v % 3 == 0) == (n % 3 == 0)
        kernel_cases += 1

    rng = random.Random(603213)
    projective_cases = 0
    for case in range(512):
        y = rng.randrange(1, 16)
        r, t = 12*y, 12*y+1
        if case % 2:
            word = tuple(rng.choice((-4,-3,-2,-1,1,2,3,4)) for _ in range(rng.randrange(15)))
            P = matrix_word(word, images)
        else:
            n = rng.randrange(-12, 13)
            P = gram.mm(power(B, n), target(r))
        out = gram.mv(P, (-1, t))
        exponent = stabilizer_power(P, r)
        assert (out[0] == 0) == (exponent is not None)
        if exponent is not None:
            assert out == (0, 1)
            assert P == gram.mm(power(B, exponent), target(r))
        projective_cases += 1

    ambiguity_cases = rejected_shift = rejected_vertex = 0
    for y, n, m in product(range(1, 13), range(-5, 6), range(-5, 6)):
        L = free.shifted_a(y)
        P = free.multiply(free.power(free.B, n), L)
        Q = free.multiply(free.power(free.B, m), L)
        relation = free.multiply(free.inverse(free.A), P, free.A, free.inverse(Q))
        vertices, shift = free.semidirect_coordinates(relation)
        assert shift == n-m
        expected_vertices = free.free_graph_reduce(((0,-1),(y-n,1),(-n,1),(y-n,-1)))
        assert vertices == expected_vertices
        if shift:
            rejected_shift += 1
        elif n:
            assert graph_abelianization(vertices) == {0:-1, -n:1}
            rejected_vertex += 1
        else:
            expected = free.conjugate(free.defining_relator(y), free.inverse(free.A))
            assert relation == expected
            assert len(vertices) == 4  # Missing-edge retraction is nontrivial.
        ambiguity_cases += 1

    # Exact accepting fibre-product witnesses for finite illustrative relators.
    accepted = 0
    for y in range(1, 13):
        L, relator = free.shifted_a(y), free.defining_relator(y)
        left = free.multiply(free.inverse(free.A), L, free.A)
        conjugator = free.multiply(free.inverse(free.A), free.inverse(L))
        factors = ((conjugator, 0, -1),)
        witness = free.pair_witness(left, factors, 2)
        generators = free.fibre_generators(2, (relator,))
        got = free.evaluate_pair_word(witness, generators)
        assert got == (left, L)
        conjugated = (free.conjugate(got[0], free.A), got[1])
        assert conjugated == (L, L)
        pair = tuple(matrix_word(w, {1:U,2:B}) for w in conjugated)
        assert pair == (target(12*y), target(12*y))
        assert scalar(pair, 12*y+1) == 0
        R = sentinel(12*y+1)
        assert not any(any(row) for row in gram.mm(gram.mm(R, lift(pair)), R))
        # One block alone always accepts, already for the free quotient.
        Q = gram.mm(gram.mm(gram.inv(U), pair[0]), U)
        assert gram.mv(pair[0], (-1,12*y+1)) == (0,1)
        assert gram.mv(Q, (-1,12*y+1))[0] != 0
        accepted += 1
    return dict(ambient_free_words=kernel_cases, projective_stabilizer_cases=projective_cases,
                ambiguity_cases=ambiguity_cases, rejected_by_shift=rejected_shift,
                rejected_by_vertex_abelianization=rejected_vertex,
                finite_relator_accepting_witnesses=accepted,
                one_block_false_positive_cases=accepted)


def arithmetic_checks():
    rng = random.Random(603214)
    assert gram.counts(loader()) == dict(M=2,A=1,operations=3)
    assert gram.counts(loader()[:2]) == dict(M=1,A=1,operations=2)
    load_cases = 0
    for alpha, beta, x in product((1,12,24,96), (1,12,48), range(1,33)):
        env = gram.execute(loader(alpha,beta), {'x':x})
        t = alpha*x+beta+1
        assert (env['input_t'],env['input_t2']) == (t,t*t)
        assert min(column(t)) > 0
        assert sentinel(t) == tuple((v,0,0,v,0,0) for v in column(t))
        assert gram.mm(sentinel(t),sentinel(t)) == tuple(tuple(2*v for v in row) for row in sentinel(t))
        load_cases += 1
    negative_target = tuple(tuple(-v for v in row) for row in target(12))
    assert gram.mv(negative_target,(-1,13)) == (0,-1)
    assert scalar((negative_target,target(12)),13) == 0
    matrix_cases = zero_cases = 0
    small = [((a,b),(c,d)) for a,b,c,d in product(range(-2,3),repeat=4) if a*d-b*c == 1]
    zero6 = tuple((0,)*6 for _ in range(6))
    for case in range(512):
        t = rng.randrange(2,60)
        pair = (rng.choice(small),rng.choice(small))
        actual = sum(gram.mv(P,(-1,t))[0]**2 for P in pair)
        assert scalar(pair,t) == actual >= 0
        right = (rng.choice(small),rng.choice(small))
        assert gram.mm(lift(pair),lift(right)) == lift(tuple(gram.mm(a,b) for a,b in zip(pair,right)))
        R = sentinel(t)
        segments = [pair,right,pair]
        if case%2 == 0:
            segments[1] = (target(t-1),target(t-1))
        dense = lift(segments[0])
        for segment in segments[1:]:
            dense = gram.mm(gram.mm(dense,R),lift(segment))
        scalar_middle = scalar(segments[1],t)
        outer = gram.mm(gram.mm(lift(segments[0]),R),lift(segments[-1]))
        assert dense == tuple(tuple(scalar_middle*v for v in row) for row in outer)
        assert (dense == zero6) == (scalar_middle == 0)
        zero_cases += scalar_middle == 0
        matrix_cases += 1

    fixed_cases = 0
    for case in range(256):
        word = [(rng.randrange(2),rng.choice(('upper','lower')),rng.choice((-1,1)))
                for _ in range(rng.randrange(1,18))]
        p = build_fixed_word(word)
        ell = len(word)
        assert gram.counts(p['source']) == dict(M=2,A=5*ell+5,operations=5*ell+7)
        assert len(p['auxiliaries']) == len(p['comparisons']) == 2*ell+1
        sos,out = gram.polynomial_source(p)
        assert gram.counts(sos) == dict(M=2*ell+3,A=9*ell+6,operations=11*ell+9)
        x = rng.randrange(1,6)
        z = fixture(p,x)
        residual = gram.residuals(p,gram.execute(sos,z))
        assert not any(residual[:-1])
        assert residual[-1] == scalar(gram.direct_pair(word),24*x+13)
        z = {k:rng.randrange(1,50) for k in ['x']+p['auxiliaries']}
        t = 24*z['x']+13
        state = [(1,t,t*t),(1,t,t*t)]
        manual = []
        for k,(block,axis,sign) in enumerate(word):
            a,b,c = state[block]
            following_b = z[f'B{k}']-z['D']
            following_diag = z[f'A{k}']-1
            expected_b = b-sign*(c if axis=='upper' else a)
            expected_diag = (a if axis=='upper' else c)-sign*b-sign*following_b
            manual += [expected_b-following_b,expected_diag-following_diag]
            state[block] = ((following_diag,following_b,c) if axis=='upper'
                            else (a,following_b,following_diag))
        manual.append(state[0][0]+state[1][0])
        env = gram.execute(sos,z)
        assert gram.residuals(p,env) == manual
        assert env[out] == sum(v*v for v in manual)
        samples = [gram.execute(sos,dict(z,x=j))[out] for j in range(6)]
        for _ in range(4):
            samples = [b-a for a,b in zip(samples,samples[1:])]
        assert samples[0] == samples[1] > 0
        fixed_cases += 1

    accepting_words = 0
    for x in range(1,4):
        r = 24*x+12
        word = []
        for block in (0,1):
            word += [(block,'lower',1)]*r+[(block,'upper',1)]+[(block,'lower',-1)]*r
        p = build_fixed_word(word)
        z = fixture(p,x)
        assert gram.direct_pair(word) == (target(r),target(r))
        assert not any(gram.residuals(p,gram.execute(p['source'],z)))
        wrong = fixture(p,x+1)
        assert gram.residuals(p,gram.execute(p['source'],wrong))[-1] > 0
        # The accepting rank-one Gram state has an actual zero diagonal.
        assert gram.mv(gram.sym(target(r)),(1,r+1,(r+1)**2)) == (0,0,1)
        accepting_words += 1
    p0 = build_fixed_word([])
    assert gram.residuals(p0,gram.execute(p0['source'],fixture(p0,1))) == [2]
    return dict(loader_cases=load_cases, dense_scalar_and_sentinel_cases=matrix_cases,
                zero_sentinel_cases=zero_cases, positive_fixed_word_and_manual_cases=fixed_cases,
                accepted_words_and_wrong_input_tests=accepting_words,
                rank_one_zero_diagonal_checked=True, empty_word_rejected=True)


def verify():
    return dict(status='PASS', dimension=6,
                vector_loader=gram.counts(loader()[:2]),
                scalar_and_mortality_loader=gram.counts(loader()),
                input_degree=2, group=group_checks(), arithmetic=arithmetic_checks(),
                fixed_nonempty_word_graph='2M+(5ell+5)A=5ell+7',
                fixed_nonempty_word_polynomial='(2ell+3)M+(9ell+6)A=11ell+9',
                fixed_nonempty_word_degree=4, fixed_word_witnesses='2ell+1',
                fixed_word_equations='2ell+1',
                scope='Fixed universal subgroup is inherited abstractly; numerical universal alphabet, '
                      'variable word selection and uniform history remain unpaid.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:assert json.loads(path.read_text())==result
    print(json.dumps(result,indent=2,sort_keys=True))
