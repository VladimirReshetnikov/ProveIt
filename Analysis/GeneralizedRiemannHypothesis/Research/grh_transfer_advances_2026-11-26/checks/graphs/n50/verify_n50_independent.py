#!/usr/bin/env python3
"""Independent exact replay and eigenvalue isolation for the C_50 certificate.

The local determinant algorithm sums signed permutation products. It does not
use Schur complements. Eigenvalue counts use exact fraction-free elimination
and Sylvester inertia. Only the Python standard library is required.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import json


def shifted_path_det(word, sign, numerator, denominator):
    order = len(word) + 2
    totals = {0:1}
    for row in range(order):
        fresh = defaultdict(int)
        for used, coefficient in totals.items():
            for column in range(max(0,row-2),min(order,row+3)):
                if used & (1<<column):
                    continue
                new_used = used | (1<<column)
                inaccessible = (1<<max(0,row-1))-1
                if new_used & inaccessible != inaccessible:
                    continue
                distance = abs(row-column)
                if distance == 0:
                    entry = numerator
                else:
                    edge = 1 if distance == 1 else word[min(row,column)]
                    entry = sign*denominator*edge
                inversions = (used>>(column+1)).bit_count()
                fresh[new_used] += coefficient*entry*((-1)**inversions)
        totals = fresh
    return totals[(1<<order)-1]


def decode(word):
    return tuple(1 if x == '+' else -1 for x in word)


def matrix_from_triangle(word):
    n = len(word)
    a = [[0]*n for _ in range(n)]
    for i,t in enumerate(word):
        a[i][(i+1)%n] = a[(i+1)%n][i] = 1
        a[i][(i+2)%n] = a[(i+2)%n][i] = t
    return a


def shifted_inertia(matrix, r, sign):
    n = len(matrix)
    a = [[r.numerator*(i == j) + r.denominator*sign*matrix[i][j]
          for j in range(n)] for i in range(n)]
    last = 1
    minors = [1]
    for k in range(n):
        pivot = a[k][k]
        assert pivot != 0
        minors.append(pivot)
        for i in range(k+1,n):
            for j in range(k+1,n):
                value = a[i][j]*pivot-a[i][k]*a[k][j]
                a[i][j], remainder = divmod(value,last)
                assert remainder == 0
        last = pivot
    negative = sum(a*b < 0 for a,b in zip(minors,minors[1:]))
    return negative, minors


def evaluate(coefficients, value):
    result = 0
    for coefficient in coefficients:
        result = result*value+coefficient
    return result


def main():
    base = Path(__file__).parent
    data = json.loads((base/'certificate_n50.json').read_text())
    numerator, denominator = data['threshold']
    states = {()}
    counts = [1]
    for length in range(1,data['window_triangle_length']+1):
        states = {word+(t,) for word in states for t in (-1,1)
                  if all(shifted_path_det(word+(t,),s,numerator,denominator)>0
                         for s in (-1,1))}
        counts.append(len(states))
        print('permutation path length',length,len(states),flush=True)
    assert counts == data['path_counts']
    assert states == {decode(w) for w in data['path_words']}
    print('All local survivors agree with the independent Schur certificate.')

    winner = data['minimizing_necklaces'][1]
    word = decode(winner['word'])
    short_word = decode('--+-++-+')*6 + decode('-+')
    assert word == short_word
    matrix = matrix_from_triangle(word)
    coefficients = winner['charpoly_descending']
    assert all(coefficients[k] == 0 for k in range(1,51,2))
    q = coefficients[::2]
    # Exact decimal endpoints. Counts refer to eigenvalues above r (sign=-1)
    # and below -r (sign=+1), respectively.
    lower = Fraction(2811568906156,10**12)
    upper = Fraction(2811568906157,10**12)
    results = []
    for label,r in [('lower',lower),('upper',upper)]:
        for sign in (-1,1):
            negative,minors = shifted_inertia(matrix,r,sign)
            assert negative == (1 if label == 'lower' else 0)
            # The final shifted determinant agrees with the Newton polynomial.
            expected = evaluate(coefficients,r)*(r.denominator**50)
            assert expected.denominator == 1
            assert minors[-1] == expected.numerator
            results.append({'endpoint':label,'r':[r.numerator,r.denominator],
                            'sign':sign,'negative_eigenvalues':negative,
                            'leading_minors':minors})
            print(label,'shift sign',sign,'negative eigenvalues',negative)
    assert evaluate(q,lower*lower) < 0
    assert evaluate(q,upper*upper) > 0
    # The alternating-family optimum is strictly larger. Since pi < 22/7,
    # cos(pi/50) > 1-(11/175)^2/2 and cos(2*pi/50) > 1-2*(11/175)^2.
    v = Fraction(11,175)
    alternating_square_lower = 4*((1-v*v/2)**2+(1-2*v*v)**2)
    assert alternating_square_lower > Fraction(2814,1000)**2
    artifact = {'interval_lower':[lower.numerator,lower.denominator],
                'interval_upper':[upper.numerator,upper.denominator],
                'Q_descending':q,'inertia_certificates':results,
                'candidate_triangle_word':'--+-++-+'*6+'-+',
                'candidate_hamilton_holonomy':1,
                'alternating_family_radius_strict_lower_bound':[1407,500],
                'scope':'rho is the unique positive eigenvalue in the stated interval, and sqrt of the largest root of Q.'}
    (base/'root_isolation.json').write_text(json.dumps(artifact,indent=2)+'\n')
    print('Certified: 2.811568906156 < rho_min < 2.811568906157.')
    print('The interval contains exactly one positive eigenvalue.')
    print('Q has degree',len(q)-1)
    print('The alternating-family optimum is strictly greater than 2.814.')


if __name__ == '__main__':
    main()
