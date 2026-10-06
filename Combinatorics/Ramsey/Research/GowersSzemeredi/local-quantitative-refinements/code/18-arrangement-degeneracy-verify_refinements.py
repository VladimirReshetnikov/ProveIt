#!/usr/bin/env python3
"""Exact finite checks for the accompanying Gowers-refinements article.

Only the Python standard library is needed. These checks corroborate the
proofs; they are not a formal verification of the general theorems.
Run: python3 verify_refinements.py --output verification_results.json
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, gcd
from functools import reduce
import argparse
import json


def cube_constants(d):
    r = (6**d - 2*4**d + 2**d) // 8
    b = 2**d * (2**d-1) * (2**d-2) // 24
    q = (8**d - 3*6**d + 3*4**d - 2**d) // 6
    s = (10**d - 4*8**d + 6*6**d - 4*4**d + 2**d) // 24
    return dict(dimension=d, rectangles=r, binary_planes=b,
                five_circuits=q, ternary_exceptions=s)


def rank_mod(rows, p):
    a = [[x % p for x in row] for row in rows]
    if not a:
        return 0
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inv = pow(a[row][col], -1, p)
        a[row] = [(v*inv) % p for v in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                z = a[i][col]
                a[i] = [(u-z*v) % p for u, v in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def cube_subset_classification(d=4):
    vertices = list(product((0, 1), repeat=d))
    totals = {"rectangles": 0, "binary_extra": 0,
              "five_circuits": 0, "ternary_extra": 0}
    for s in combinations(vertices, 4):
        rows = [[1]*4] + [list(v) for v in zip(*s)]
        ordinary = rank_mod(rows, 5)
        if ordinary == 3:
            totals["rectangles"] += 1
        elif rank_mod(rows, 2) == 3:
            totals["binary_extra"] += 1
    for s in combinations(vertices, 5):
        rows = [[1]*5] + [list(v) for v in zip(*s)]
        ordinary = rank_mod(rows, 5)
        if ordinary == 4:
            minimal = all(rank_mod([[row[j] for j in ix] for row in rows], 5) == 4
                          for ix in combinations(range(5), 4))
            totals["five_circuits"] += minimal
        elif rank_mod(rows, 3) == 4:
            totals["ternary_extra"] += 1
    c = cube_constants(d)
    assert totals == {"rectangles": c["rectangles"],
                      "binary_extra": c["binary_planes"]-c["rectangles"],
                      "five_circuits": c["five_circuits"],
                      "ternary_extra": c["ternary_exceptions"]}
    return dict(dimension=d, **totals)


def cube_coefficient_sums(f, d, degree=5):
    n = len(f)
    sums = [0]*(degree+1)
    vertices = list(product((0, 1), repeat=d))
    for args in product(range(n), repeat=d+1):
        x, hs = args[0], args[1:]
        coeffs = [1]+[0]*degree
        for e in vertices:
            v = f[(x+sum(a*b for a, b in zip(e, hs))) % n]
            for j in range(degree, 0, -1):
                coeffs[j] += v*coeffs[j-1]
        sums = [a+b for a, b in zip(sums, coeffs)]
    return [Fraction(x, n**(d+1)) for x in sums]


def model_moments(f):
    n = len(f)
    assert sum(f) == 0
    u4 = sum(f[x]*f[(x+h)%n]*f[(x+j)%n]*f[(x+h+j)%n]
             for x,h,j in product(range(n), repeat=3))
    u4 = Fraction(u4, n**3)
    t5 = sum(f[x]*f[(x+h)%n]*f[(x+j)%n]*f[(x+l)%n]*f[(x+h+j+l)%n]
             for x,h,j,l in product(range(n), repeat=4))
    t5 = Fraction(t5, n**4)
    e2 = Fraction(sum(v*((-1)**i) for i,v in enumerate(f)), n)**4 if n%2 == 0 else Fraction(0)
    e3 = Fraction(0)
    if n%3 == 0:
        g = [Fraction(sum(f[a::3]), n//3) for a in range(3)]
        e3 = sum(g[(a+b+c+d)%3]*g[a]*g[b]*g[c]*g[d]
                 for a,b,c,d in product(range(3), repeat=4)) / 3**4
    return u4, t5, e2, e3


def verify_cube_moments():
    functions = [[1,-1], [2,-1,-1], [3,-2,1,-2],
                 [4,-1,-1,-1,-1], [5,-2,1,-3,2,-3],
                 [6,-2,1,-1,-3,2,-3]]
    output = []
    for f in functions:
        u4,t5,e2,e3 = model_moments(f)
        for d in (3,4):
            c = cube_constants(d)
            actual = cube_coefficient_sums(f,d)
            fourth = c["rectangles"]*u4+(c["binary_planes"]-c["rectangles"])*e2
            fifth = c["five_circuits"]*t5+c["ternary_exceptions"]*e3
            assert actual[1:4] == [0,0,0]
            assert actual[4] == fourth, (f,d,actual[4],fourth)
            assert actual[5] == fifth, (f,d,actual[5],fifth)
            output.append(dict(order=len(f), dimension=d, f=f,
                               fourth=str(fourth), fifth=str(fifth)))
    return output


def central_trinomial(n):
    return sum(comb(n,2*j)*comb(2*j,j) for j in range(n//2+1))


def parity_constant(d):
    return (central_trinomial(2*d)-2*comb(2*d,d)+1)//2


def projective(v, p):
    a = next((x % p for x in v if x % p), None)
    if a is None:
        return None
    return tuple(x*pow(a,-1,p)%p for x in v)


def enumerate_parity_hyperplanes(d, p):
    signs = [1]*d+[-1]*d
    classes = set()
    for a in product((-1,0,1),repeat=2*d):
        if sum(a) % p:
            continue
        # Eliminate the final cross-section from signs dot r = 0.
        normal = [a[i]+a[-1]*signs[i] for i in range(2*d-1)]
        key = projective(normal,p)
        if key is not None:
            classes.add(key)
    assert len(classes) == parity_constant(d), (d,p,len(classes))
    return dict(d=d,p=p,count=len(classes))


def enumerate_certificate_classes(n, p=101):
    # Multiply coordinatewise by the universal sign pattern; it becomes 1.
    classes = set()
    for a in product((-1,0,1),repeat=n):
        key = projective([x-a[-1] for x in a[:-1]],p)
        if key is not None:
            classes.add(key)
    expected = (3**n-2**(n+1)+1)//2
    assert len(classes) == expected
    return dict(n=n,p=p,count=len(classes))


def verify_exceptional_diagonal(d=2,p=5):
    signs = [1]*d+[-1]*d
    successes = total = 0
    for prefix in product(range(p),repeat=2*d-1):
        r = prefix+(sum(signs[i]*prefix[i] for i in range(2*d-1))%p,)
        rows = [signs, [s*x % p for s,x in zip(signs,r)]]
        rank = rank_mod(rows,p)
        successes += p**(2*d-rank)
        total += p**(2*d)
    probability = Fraction(successes,total)
    predicted = Fraction(1,p*p)+Fraction(p-1,p**(2*d))
    assert probability == predicted
    return dict(d=d,p=p,probability=str(probability))


def det(matrix):
    n = len(matrix)
    answer = 0
    for perm in permutations(range(n)):
        inversions = sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        term = (-1)**inversions
        for i in range(n):
            term *= matrix[i][perm[i]]
        answer += term
    return answer


def verify_determinant_limits():
    result = []
    for n in (2,3,4):
        largest = max(abs(det([row[i*n:(i+1)*n] for i in range(n)]))
                      for row in product((0,1),repeat=n*n))
        assert largest == {2:1,3:2,4:3}[n]
        result.append(dict(size=n,max_absolute_binary_determinant=largest))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='verification_results.json')
    args = parser.parse_args()
    results = {
        'description': 'Exact finite corroboration, not general theorem certification.',
        'cube_constants': [cube_constants(d) for d in range(2,8)],
        'four_cube_subsets': cube_subset_classification(),
        'cyclic_group_moments': verify_cube_moments(),
        'parity_constants': [dict(d=d,central_trinomial=central_trinomial(2*d),
                                  leading_parity_constant=parity_constant(d))
                             for d in range(2,9)],
        'parity_hyperplane_enumeration': [enumerate_parity_hyperplanes(d,p)
                                        for d,p in [(2,5),(2,7),(3,7),(3,11),(4,11),(4,101)]],
        'certificate_class_enumeration': [enumerate_certificate_classes(n) for n in (2,4,6,8)],
        'exceptional_diagonal': [verify_exceptional_diagonal(2,p) for p in (5,7,11)],
        'binary_determinants': verify_determinant_limits(),
        'all_checks_passed': True,
    }
    with open(args.output,'w',encoding='utf8') as handle:
        json.dump(results,handle,indent=2)
        handle.write('\n')
    print(json.dumps({'all_checks_passed': True, 'output': args.output,
                      'cube_moment_cases': len(results['cyclic_group_moments']),
                      'four_cube_subsets_examined': comb(16,4)+comb(16,5)}))


if __name__ == '__main__':
    main()
