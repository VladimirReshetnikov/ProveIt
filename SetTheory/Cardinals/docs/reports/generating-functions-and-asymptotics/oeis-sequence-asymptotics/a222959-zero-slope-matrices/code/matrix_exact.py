#!/usr/bin/env python3
"""Finite exact arithmetic for centered-weight binary matrices (stdlib only)."""
from collections import Counter
from fractions import Fraction as F


def need(condition, message):
    if not condition:
        raise ValueError(message)


def dimension(n, low=2, high=14):
    need(type(n) is int and low <= n <= high, 'dimension outside documented bound')


def weights(n):
    dimension(n, 1)
    return [j - n//2 if n % 2 else 2*j - n + 1 for j in range(n)]


def alphabet(n):
    w = weights(n)
    return [tuple((mask >> j) & 1 for j in range(n))
            for mask in range(1 << n)
            if sum(w[j] for j in range(n) if (mask >> j) & 1) == 0]


def rank(rows):
    if not rows:
        return 0
    width = len(rows[0])
    need(all(len(row) == width for row in rows), 'ragged matrix')
    a = [list(map(F, row)) for row in rows]
    r = 0
    for j in range(width):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        p = a[r][j]
        a[r] = [x/p for x in a[r]]
        for i in range(r+1, len(a)):
            if a[i][j]:
                c = a[i][j]
                a[i] = [x-c*y for x,y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def determinant(matrix):
    """Bareiss integer elimination, checking each exact division."""
    n = len(matrix)
    need(all(len(row) == n for row in matrix), 'determinant requires square matrix')
    need(all(type(x) is int for row in matrix for x in row), 'integer matrix required')
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k,n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator = p*a[i][j]-a[i][k]*a[k][j]
                need(numerator % previous == 0, 'nonexact Bareiss division')
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = p
    return sign*a[-1][-1]


def design(n):
    w = weights(n)
    ell = w.index(1)
    columns = [j for j in range(n) if j != ell]
    a = [[0]*(n*n) for _ in range(2*n-1)]
    for i in range(n):
        for j in range(n):
            a[i][i*n+j] = w[j]
            if j != ell:
                a[n+columns.index(j)][i*n+j] = w[i]
    return a


def structure(n):
    """Reduced integer right inverse verifies saturation on every basis vector."""
    dimension(n)
    w = weights(n)
    S = sum(x*x for x in w)
    ell = w.index(1)
    columns = [j for j in range(n) if j != ell]
    a = design(n)
    q = [[sum(x*y for x,y in zip(row,col)) for col in a] for row in a]
    det = determinant(q)
    need(det == S**(2*n-2), 'reduced Gram determinant failure')
    for k in range(2*n-1):
        target = [int(j == k) for j in range(2*n-1)]
        right = target[:n]
        left = [0]*n
        for j, value in zip(columns,target[n:]):
            left[j] = value
        c = sum(x*y for x,y in zip(w,right))
        left[ell] = c-sum(w[j]*left[j] for j in columns)
        matrix = [right[i]*int(j == ell) + int(i == ell)*left[j]
                  -c*int(i == ell and j == ell)
                  for i in range(n) for j in range(n)]
        need([sum(x*y for x,y in zip(row,matrix)) for row in a] == target,
             'integer right inverse failure')
        # Also check the omitted full coordinate, not only the reduced map.
        need([sum(matrix[i*n+j]*w[i] for i in range(n)) for j in range(n)] == left,
             'full compatible left margin failure')
    words = alphabet(n)
    return {'n': n, 'weights': w, 'S': S, 'alphabet_size': len(words),
            'alphabet_rank': rank(words), 'integer_right_inverse_basis_vectors': 2*n-1,
            'reduced_gram_determinant': str(det)}


def local_projection(n):
    """Direct full projector products and moment contractions for 2<=n<=12."""
    dimension(n, 2, 12)
    w = weights(n)
    S = sum(x*x for x in w)
    need(S == F(n*(n*n-1), 12 if n%2 else 3), 'weight-square sum failure')
    a = [F(x*x,S) for x in w]
    s2 = sum(x*x for x in a)
    s3 = sum(x**3 for x in a)
    need(s2 == F(3*(3*n*n-7),5*n*(n*n-1)), 's2 identity failure')
    need(s3 == F(9*(3*n**4-18*n*n+31),7*n*n*(n*n-1)**2), 's3 identity failure')
    cells = [(i,j) for i in range(n) for j in range(n)]
    denominator = S*S
    p = [[((w[j]*w[l] if i==k else 0)+(w[i]*w[k] if j==l else 0))*S
          -w[i]*w[j]*w[k]*w[l] for k,l in cells] for i,j in cells]
    need(all(p[r][s] == p[s][r] for r in range(n*n) for s in range(n*n)),
         'projector symmetry failure')
    for r in range(n*n):
        for s in range(r,n*n):
            need(sum(x*y for x,y in zip(p[r],p[s])) == denominator*p[r][s],
                 'projector idempotence failure')
    h = [F(p[r][r],denominator) for r in range(n*n)]
    need(h == [a[i]+a[j]-a[i]*a[j] for i,j in cells], 'projector diagonal failure')
    need(sum(h) == 2*n-1, 'projector trace failure')
    # Integer numerators avoid rounding and repeated Fraction normalization.
    hn = [p[r][r] for r in range(n*n)]
    A = F(sum(hn[r]*hn[s]*p[r][s]**2 for r in range(n*n) for s in range(n*n)), denominator**4)
    B = F(sum(x**4 for row in p for x in row), denominator**4)
    h2 = sum(x*x for x in h)
    h3 = sum(x**3 for x in h)
    need(A == 6*s2+(2*n-12)*s2**2+6*s2**3+s2**4-4*s2**2*s3+2*s3**2, 'A contraction failure')
    need(B == (2*n-2)*s2**2+12*s2**3+s2**4+8*s3-24*s2*s3-8*s2**2*s3+12*s3**2, 'B contraction failure')
    need(h2 == 2*n*s2+2-4*s2+s2*s2, 'diagonal second moment failure')
    need(h3 == 2*n*s3+6*s2-6*s3-6*s2**2+6*s2*s3-s3**2, 'diagonal third moment failure')
    return {'n': n, 'S': S, 's2': str(s2), 's3': str(s3), 'trace': str(sum(h)),
            'A': str(A), 'B': str(B), 'sum_h2': str(h2), 'sum_h3': str(h3),
            'quartic_mean': str(h2/4), 'projector_dimension': n*n,
            'symmetric_and_idempotent': True}


def first_coefficient():
    alpha, beta = F(9,5), F(27,7)
    A, B, H = 6*alpha+2*alpha**2, 2*alpha**2, 2*beta+6*alpha
    c1 = alpha+A/4+B/12-H/3
    need(alpha/2+F(1,2) == F(7,5), 'constant exponent failure')
    need((A,B,H,c1) == (F(432,25),F(162,25),F(648,35),F(171,350)), 'first correction failure')
    return {key:str(value) for key,value in {'exponent_magnitude':F(7,5),
            'n_times_A':A, 'n_times_B':B, 'n_times_sum_h3':H,
            'quartic_mean_correction':alpha, 'c1':c1}.items()}


def count_mitm(n, allow_n9=False):
    """Count by matching positive/negative weighted row sums in packed lanes.

    Every lane sum is between zero and sum(positive weights), strictly below
    the radix. Python integers are unbounded, so there is neither a cross-lane
    carry nor a machine-word overflow. The zero-weight row contributes a
    separate alphabet factor. This is finite enumeration, not asymptotics.
    """
    dimension(n, 1, 9 if allow_n9 else 8)
    rows = alphabet(n)
    if n == 1:
        return {'n':1, 'alphabet_size':2, 'positive_row_tuples':1, 'count':2,
                'lane_bits':1, 'maximum_lane_sum':0}
    positive = [w for w in weights(n) if w > 0]
    maximum = sum(positive)
    bits = maximum.bit_length()
    need((1 << bits) > maximum, 'packed lane radix is too small')
    packed = [sum(value << (bits*j) for j,value in enumerate(row)) for row in rows]
    tuples = [0]
    for weight in positive:
        tuples = [value+weight*word for value in tuples for word in packed]
    need(len(tuples) == len(rows)**len(positive), 'tuple inventory failure')
    frequencies = Counter(tuples)
    answer = sum(count*count for count in frequencies.values())
    if n%2:
        answer *= len(rows)
    return {'n':n, 'alphabet_size':len(rows), 'positive_row_tuples':len(tuples),
            'count':answer, 'lane_bits':bits, 'maximum_lane_sum':maximum}


def count_tuple_reference(n):
    """Independent unpacked implementation, bounded through n=7."""
    dimension(n,1,7)
    rows = alphabet(n)
    values = [(0,)*n]
    for weight in weights(n):
        if weight > 0:
            values = [tuple(x+weight*y for x,y in zip(value,row))
                      for value in values for row in rows]
    result = sum(c*c for c in Counter(values).values())
    return result*len(rows) if n%2 else result
