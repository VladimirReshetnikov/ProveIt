#!/usr/bin/env python3
"""A two-reset four-dimensional universal interface; unrestricted reset failure.

The fixed universal matrix alphabet is inherited abstractly. Exact finite
free-group and one-relator fixtures check constructions, not universality.
"""
import argparse
from itertools import product
import json
from pathlib import Path
import random

import group_commutator_universal_substrate as free
import group_gram_zero_mortality as gram
import group_projective_zero_mortality6 as projective


I = gram.I2
C = ((-1, 0), (0, 1))
ROW = (1, 0)


def blocks(matrices):
    dimension = sum(len(a) for a in matrices)
    result = [[0]*dimension for _ in range(dimension)]
    offset = 0
    for a in matrices:
        for i, row in enumerate(a):
            for j, value in enumerate(row):
                result[offset+i][offset+j] = value
        offset += len(a)
    return tuple(map(tuple, result))


def outer(v, u):
    return tuple(tuple(a*b for b in u) for a in v)


def scale(a, factor):
    return tuple(tuple(factor*x for x in row) for row in a)


def zero(a):
    return all(x == 0 for row in a for x in row)


def conjugate(a):
    return gram.mm(gram.mm(C, a), C)


def alphabet_matrix(pair):
    return blocks(tuple(conjugate(a) for a in pair))


def reset(t):
    return blocks((((1, 0), (t, 0)),)*2)


def loader(alpha=24, beta=12):
    assert alpha > 0 and beta > 0
    return [('scaled', '*', alpha, 'x'), ('t', '+', 'scaled', beta+1)]


def reset_word(segments, R):
    """A0 R A1 R ... R Ak, with k=len(segments)-1."""
    value = blocks(segments[0])
    for pair in segments[1:]:
        value = gram.mm(gram.mm(value, R), blocks(pair))
    return value


def bridge(pair, t):
    R = reset(t)
    return gram.mm(gram.mm(R, alphabet_matrix(pair)), R)


def pair_matrices(pair):
    return tuple(projective.matrix_word(word, {1: projective.U, 2: projective.B})
                 for word in pair)


def fibre_pair(word, relators=()):
    raw = free.evaluate_pair_word(word, free.fibre_generators(2, relators))
    return free.conjugate(raw[0], free.A), raw[1]


def factorization_checks():
    rng = random.Random(420092)
    small = [((a,b),(c,d)) for a,b,c,d in product(range(-2,3), repeat=4)
             if a*d-b*c == 1]
    cases = zero_cases = forced_cases = no_reset = one_reset = 0
    for case in range(1536):
        count = rng.randrange(1, 5)
        k = rng.randrange(7)
        if case % 2:
            # Force exact individual zeros with independently chosen supports.
            columns = [(1, rng.randrange(1, 12)) for _ in range(count)]
            rows = [ROW]*count
        else:
            columns, rows = [], []
            for _ in range(count):
                for dest in (columns, rows):
                    value = (0,0)
                    while value == (0,0):
                        value = tuple(rng.randrange(-3,4) for _ in range(2))
                    dest.append(value)
        segments = []
        for j in range(k+1):
            row = []
            for i in range(count):
                if case % 2 and 0 < j < k and rng.randrange(3) == 0:
                    t = columns[i][1]
                    row.append(((-t,1),(-1,0)))
                    forced_cases += 1
                else:
                    row.append(rng.choice(small))
            segments.append(tuple(row))
        R = blocks(tuple(outer(v,u) for v,u in zip(columns,rows)))
        actual = reset_word(segments,R)
        if k == 0:
            assert not zero(actual)
            no_reset += 1
        else:
            predicted, coverage = [], []
            for i in range(count):
                coefficient = 1
                covered = False
                for segment in segments[1:-1]:
                    value = gram.dot(rows[i],gram.mv(segment[i],columns[i]))
                    coefficient *= value
                    covered |= value == 0
                left = gram.mv(segments[0][i],columns[i])
                right = tuple(sum(rows[i][h]*segments[-1][i][h][j] for h in range(2))
                              for j in range(2))
                assert left != (0,0) and right != (0,0)
                predicted.append(scale(outer(left,right),coefficient))
                coverage.append(covered)
            assert actual == blocks(predicted)
            assert zero(actual) == all(coverage)
            zero_cases += zero(actual)
            if k == 1:
                assert not zero(actual)
                one_reset += 1
        cases += 1
    return dict(dense_factorization_cases=cases, zero_products=zero_cases,
                deliberately_zero_block_segments=forced_cases,
                no_reset_invertible_cases=no_reset, one_reset_nonzero_cases=one_reset)


def input_and_separation_checks():
    rng = random.Random(412073)
    loader_cases = separation_cases = 0
    for case in range(512):
        p, x = rng.randrange(24), rng.randrange(1,100)
        alpha, beta = 12*2**(p+1),12*2**p
        source = loader(alpha,beta)
        assert gram.counts(source) == dict(M=1,A=1,operations=2)
        env = gram.execute(source,dict(x=x))
        r,t = alpha*x+beta,env['t']
        assert t == r+1 and t > 0
        R = reset(t)
        assert all(value >= 0 for row in R for value in row)
        assert gram.mm(R,R) == R and not zero(R)
        signed_reset = outer((-1,t),ROW)
        assert scale(conjugate(signed_reset),-1) == ((1,0),(t,0))
        loader_cases += 1

        # All these words use only conjugates of diagonal generators, so no
        # relator or membership oracle is needed to build the three-reset zero.
        y = rng.randrange(1,41)
        r,t = 12*y,12*y+1
        L = free.shifted_a(y)
        w1 = free.multiply(free.inverse(free.A),L,free.A)
        w2 = L
        pair1, pair2 = fibre_pair(w1), fibre_pair(w2)
        assert pair1 == (L,w1)
        assert pair2 == (free.conjugate(L,free.A),L)
        P1,P2 = pair_matrices(pair1),pair_matrices(pair2)
        expected1,expected2 = (0,r*(r*r+2*r+2)),(r*(r*r-2),0)
        assert tuple(gram.mv(A,(-1,t))[0] for A in P1) == expected1
        assert tuple(gram.mv(A,(-1,t))[0] for A in P2) == expected2
        for pair,expected in ((P1,expected1),(P2,expected2)):
            assert tuple(gram.mv(conjugate(A),(1,t))[0] for A in pair) == tuple(-v for v in expected)
            assert not zero(bridge(pair,t))
        R = reset(t)
        separated = gram.mm(gram.mm(bridge(P1,t),alphabet_matrix(P2)),R)
        assert zero(separated)
        # With invertible exterior words the zero remains zero, while each
        # individual two-reset product still has a nonzero block.
        exterior = alphabet_matrix((projective.U,projective.B))
        assert zero(gram.mm(gram.mm(exterior,separated),exterior))
        separation_cases += 1
    return dict(ordinary_program_input_loader_cases=loader_cases,
                fixed_diagonal_word_three_reset_zeros=separation_cases,
                neither_internal_word_has_synchronized_zeros=True,
                idempotent_and_nonnegative_reset_checked=True)


def finite_group_checks():
    rejected = accepted = wrong_input = 0
    # Empty-relator free quotient: no positive target belongs to the commutator
    # language. This bounded enumeration supplements, not proves, the theorem.
    for word in free.reduced_words(2,6):
        pair = pair_matrices(fibre_pair(word))
        for y in range(1,5):
            values = tuple(gram.mv(A,(-1,12*y+1))[0] for A in pair)
            assert values != (0,0)
            assert not zero(bridge(pair,12*y+1))
            rejected += 1
    # One-relator accepting fibres: verify actual finite-alphabet word witnesses.
    for y in range(1,25):
        L,relator = free.shifted_a(y),free.defining_relator(y)
        left = free.multiply(free.inverse(free.A),L,free.A)
        by = free.multiply(free.inverse(free.A),free.inverse(L))
        witness = free.pair_witness(left,((by,0,-1),),2)
        pair = fibre_pair(witness,(relator,))
        assert pair == (L,L)
        matrices = pair_matrices(pair)
        assert zero(bridge(matrices,12*y+1))
        assert not zero(bridge(matrices,12*(y+1)+1))
        # The six-dimensional rank-one adapter preserves synchronization even
        # under unrestricted resets; compare its single middle scalar.
        assert projective.scalar(matrices,12*y+1) == 0
        assert projective.scalar(matrices,12*(y+1)+1) > 0
        accepted += 1
        wrong_input += 1
    return dict(empty_relator_two_reset_rejections=rejected,
                finite_relator_accepting_words=accepted,
                accepted_word_wrong_input_rejections=wrong_input,
                universal_alphabet_numerically_instantiated=False)


def verify():
    return dict(status='PASS',dimension=4,reset_rank=2,reset_idempotent=True,
                reset_nonnegative=True,input_degree=1,
                reset_loader=gram.counts(loader()),loader_positive_auxiliaries=0,
                universal_language='R_x F* R_x; equivalently zero with at most two resets',
                unrestricted_mortality='true for every input; a three-reset zero is explicit',
                minimum_reset_count='2 for members; 3 for nonmembers',
                factorization=factorization_checks(),input=input_and_separation_checks(),
                finite_groups=finite_group_checks(),
                scope='One fixed invertible alphabet and one input reset matrix. '
                      'Universal alphabet inherited abstractly; selected words and the '
                      'two-reset language constraint are not arithmetically encoded here.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-receipt',action='store_true')
    args=parser.parse_args()
    result=verify()
    path=Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == result
    print(json.dumps(result,indent=2,sort_keys=True))
