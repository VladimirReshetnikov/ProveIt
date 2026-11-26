#!/usr/bin/env python3
"""Exact local-window certificate for the minimum signing radius on C_50(1,2).

Only Python's standard library is needed. No numerical eigenvalue routines.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

N = 50
LENGTH = N - 4
T = Fraction(7029, 2500)


def encode(word):
    return ''.join('+' if t == 1 else '-' for t in word)


def canonical(word):
    return min(word[k:] + word[:k] for k in range(len(word)))


def extend(block, sign):
    a, b, c = block
    assert a > 0
    return c - b*b/a, -1 + b*sign/a, T - 1/a


def positive(block):
    a, b, c = block
    return a > 0 and a*c > b*b


def enumerate_paths():
    initial = (T, Fraction(-1), T)
    assert positive(initial)
    frontier = {(): (initial, initial)}
    counts = [1]
    for length in range(1, LENGTH + 1):
        children = {}
        for word, (minus, plus) in frontier.items():
            for sign in (-1, 1):
                left = extend(minus, sign)
                right = extend(plus, -sign)
                if positive(left) and positive(right):
                    children[word + (sign,)] = left, right
        frontier = children
        counts.append(len(frontier))
        print(f'path length {length}: {len(frontier)}', flush=True)
    return set(frontier), counts


def enumerate_cycles(allowed):
    cycles = set()
    for word in allowed:
        for suffix in product((-1, 1), repeat=N-LENGTH):
            candidate = word + suffix
            doubled = candidate + candidate
            if all(doubled[k:k+LENGTH] in allowed for k in range(N)):
                cycles.add(canonical(candidate))
    return sorted(cycles)


def adjacency(word, alpha):
    signs = [1]*(N-1) + [alpha]
    matrix = [[0]*N for _ in range(N)]
    for i in range(N):
        j = (i+1) % N
        matrix[i][j] = matrix[j][i] = signs[i]
        j = (i+2) % N
        matrix[i][j] = matrix[j][i] = word[i]*signs[i]*signs[(i+1) % N]
    assert all(sum(x*x for x in row) == 4 for row in matrix)
    return matrix


def sylvester_shift(matrix, side):
    """Exact fraction-free elimination; each pivot is a leading minor.

    Return all tested leading minors, stopping on the first nonpositive one.
    All previous pivots are positive, so no row exchange is needed.
    """
    a = [[T.numerator*(i == j) + side*T.denominator*matrix[i][j]
          for j in range(N)] for i in range(N)]
    previous = 1
    minors = []
    for k in range(N):
        pivot = a[k][k]
        minors.append(pivot)
        if pivot <= 0:
            return False, minors
        if k+1 < N:
            for i in range(k+1, N):
                for j in range(k+1, N):
                    numerator = a[i][j]*pivot - a[i][k]*a[k][j]
                    a[i][j], rest = divmod(numerator, previous)
                    assert rest == 0
            previous = pivot
    return True, minors


def charpoly(matrix):
    """Newton identities from exact integer traces, with sparse left products."""
    sparse = [[(j,x) for j,x in enumerate(row) if x] for row in matrix]
    power = [[int(i == j) for j in range(N)] for i in range(N)]
    traces = [0]
    coefficients = [1]
    for k in range(1,N+1):
        power = [[sum(x*power[j][col] for j,x in sparse[i])
                  for col in range(N)] for i in range(N)]
        traces.append(sum(power[i][i] for i in range(N)))
        numerator = -sum(coefficients[k-i]*traces[i] for i in range(1,k+1))
        coefficient, remainder = divmod(numerator,k)
        assert remainder == 0
        coefficients.append(coefficient)
    return coefficients, traces


def main():
    allowed, counts = enumerate_paths()
    cycles = enumerate_cycles(allowed)
    print('cyclic necklaces:', len(cycles), flush=True)
    tests = []
    winners = []
    for word in cycles:
        for alpha in (-1,1):
            matrix = adjacency(word,alpha)
            plus, pminors = sylvester_shift(matrix,1)
            minus, mminors = sylvester_shift(matrix,-1)
            record = {'word':encode(word),'alpha':alpha,
                      'below_threshold':plus and minus,
                      'plus_leading_minors':pminors,
                      'minus_leading_minors':mminors}
            tests.append(record)
            print('whole cycle', encode(word), alpha, plus and minus, flush=True)
            if plus and minus:
                coefficients, traces = charpoly(matrix)
                winners.append({'word':encode(word),'alpha':alpha,
                                'charpoly_descending':coefficients,'traces':traces})
    assert len(winners) == 2
    assert all(w['alpha'] == 1 for w in winners)
    words = [tuple(1 if t == '+' else -1 for t in w['word']) for w in winners]
    assert canonical(tuple(-t for t in words[0])) == words[1]
    rotations = [{w[j:]+w[:j] for j in range(N)} for w in words]
    assert len(rotations[0]) == len(rotations[1]) == N
    assert rotations[0].isdisjoint(rotations[1])
    # Sign reversal of every edge takes a triangle word to its negative and
    # keeps alpha because N is even. Hence the two surviving spectra have
    # identical absolute values and both are global minimizers.
    a = winners[0]['charpoly_descending']
    b = winners[1]['charpoly_descending']
    assert b == [c*((-1)**k) for k,c in enumerate(a)]
    record = {'n':N,'threshold':[T.numerator,T.denominator],
              'window_triangle_length':LENGTH,'path_counts':counts,
              'path_words':[encode(w) for w in sorted(allowed)],
              'cyclic_necklaces':[encode(w) for w in cycles],
              'whole_cycle_tests':tests,'minimizing_necklaces':winners,
              'number_of_labeled_minimizing_switching_classes':2*N}
    Path(__file__).with_name('certificate_n50.json').write_text(json.dumps(record,indent=2)+'\n')
    print('Certified global minimizing necklaces:', len(winners))
    print('Certified labeled minimizing switching classes:', 2*N)
    print('Characteristic polynomials computed by exact Newton identities.')


if __name__ == '__main__':
    main()
