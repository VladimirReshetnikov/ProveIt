#!/usr/bin/env python3
"""Independent finite controls for the new carry-coding theorem.

This uses small source coefficients, never the inaccessible accepting
computation of the consistency instance. It tests the mathematical source
interface on a two-equation toy system, including overlapping non-target
coefficient blocks and deliberately malformed packed words.
"""
from itertools import product
from math import factorial
import json
import random


def no_carry(a, b):
    assert a >= 0 and b >= 0
    return (a & b) == 0


def run():
    # {0,1,3} is B2. The second row has a positive constant term.
    weights = (1, 3)
    rows = ({(1, 0): 1, (0, 1): 1, (0, 0): -5},
            {(0, 0): 6, (1, 1): -1})
    t = 3
    targets = (6, 13)  # distance 2t+1, not 4t+1
    span = 19
    beta = 4096
    cases = invalid = accepting = 0
    rng = random.Random(20261023)
    for b in (4, 16):
        B = beta * b*b
        N0 = B**(t+1)
        N1 = 4 * B**(span+1)
        N = N0*N1
        cap = b*B**t
        D = 0
        for row, E in zip(rows, targets):
            for alpha, a in row.items():
                c = a*factorial(2-sum(alpha))
                for v in alpha:
                    c *= factorial(v)
                D += c * B**(E-sum(v*w for v,w in zip(alpha,weights)))
        assert D > 0
        mask = N0-1-(b-1)*sum(B**w for w in weights)
        target = (B-2)*sum(B**E for E in targets)
        T = mask + target*N0
        assert 0 <= T < N

        def source(g):
            J = 2*(1+g)**2*D + sum(B**(i+1) for i in range(span+1))
            S = g + J*N0
            R = (S+T+1)*N+T+1
            X = (N-1)*R
            assert 0 < J < N1 and 0 <= S < N
            assert X % 3 == 0 and X > 3*b
            assert N*N > max(b, 256)
            assert no_carry(S,T) == (no_carry(g,mask) and no_carry(J,target))
            # Kummer: valuation_2 binomial(2X,X) = popcount(X).
            binomial_divisibility = X.bit_count() >= 2*(N.bit_length()-1)
            assert binomial_divisibility == no_carry(S,T)
            return binomial_divisibility

        for z in product(range(b), repeat=2):
            g = sum(v*B**w for v,w in zip(z,weights))
            assert g < cap
            ok = z[0]+z[1] == 5 and z[0]*z[1] == 6
            assert source(g) == ok
            accepting += int(ok)
            cases += 1
        # Arbitrary words in the permitted broad interval have valid bounds.
        # If the digit mask rejects one, the final binomial test must reject it.
        for _ in range(200):
            g = rng.randrange(2*cap)
            result = source(g)
            if not no_carry(g,mask):
                assert not result
                invalid += 1
            cases += 1
    return {'status':'PASS','cases':cases,'accepting_cases':accepting,
            'malformed_words_rejected':invalid,
            'overlapping_product_supports':[[0,12],[7,19]],
            'targets':list(targets),
            'scope':'Finite controls of the source identity; no K215 run or consistency claim.'}


if __name__ == '__main__':
    if not __debug__: raise SystemExit('Run without -O: audit assertions are required.')
    print(json.dumps(run(),indent=2))
