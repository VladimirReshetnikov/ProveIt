#!/usr/bin/env python3
"""Exact finite identities used by the relation-space universality proof.

Pure Python, no third-party dependencies. Fields supported: F_2, F_3,
F_4=F_2[z]/(z^2+z+1), represented by 0,1,2,3 in the last case.
These are finite checks of identities, not a numerical proof of a limit.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse
import json


class Field:
    def __init__(self, q):
        if q not in (2, 3, 4):
            raise ValueError('Only q=2,3,4 are implemented')
        self.q = q
        self.add_table = [[self._add(a,b) for b in range(q)] for a in range(q)]
        self.mul_table = [[self._mul(a,b) for b in range(q)] for a in range(q)]
        self.neg_table = [next(b for b in range(q) if self.add_table[a][b] == 0) for a in range(q)]
        self.inv_table = [0] + [next(b for b in range(1,q) if self.mul_table[a][b] == 1) for a in range(1,q)]

    def _add(self,a,b):
        return a ^ b if self.q == 4 else (a+b) % self.q

    def _mul(self,a,b):
        if self.q != 4:
            return a*b % self.q
        p = 0
        while b:
            if b & 1:
                p ^= a
            b >>= 1
            a <<= 1
        # Reduce by z^2+z+1, whose binary encoding is 7.
        if p & 4:
            p ^= 7
        return p

    def add(self,a,b):
        return self.add_table[a][b]

    def mul(self,a,b):
        return self.mul_table[a][b]

    def sub(self,a,b):
        return self.add_table[a][self.neg_table[b]]

    def dot(self,a,b):
        z = 0
        for x,y in zip(a,b):
            z = self.add_table[z][self.mul_table[x][y]]
        return z

    def char_exponent(self,a):
        """Exponent for a fixed nontrivial additive character."""
        if self.q == 4:
            return self.add_table[a][self.mul_table[a][a]]
        return a


def rank(matrix,F):
    a = [row[:] for row in matrix]
    nr = len(a)
    nc = len(a[0]) if nr else 0
    r = 0
    for col in range(nc):
        pivot = next((i for i in range(r,nr) if a[i][col]),None)
        if pivot is None:
            continue
        a[r],a[pivot] = a[pivot],a[r]
        inv = F.inv_table[a[r][col]]
        a[r] = [F.mul(v,inv) for v in a[r]]
        for i in range(nr):
            if i != r and a[i][col]:
                c = a[i][col]
                a[i] = [F.sub(x,F.mul(c,y)) for x,y in zip(a[i],a[r])]
        r += 1
        if r == nr:
            break
    return r


def gauss(n,k,q):
    if k < 0 or k > n:
        return 0
    ans = 1
    for j in range(k):
        ans = ans * (q**(n-j)-1) // (q**(j+1)-1)
    return ans


def g(n,q):
    ans = Fraction(1)
    for i in range(1,n+1):
        ans *= 1-Fraction(1,q**i)
    return ans


def character_norm_squared(value_counts,F):
    """Exact norm of sum_x psi(f(x)); returns an integer."""
    exponents = Counter()
    for value,count in value_counts.items():
        exponents[F.char_exponent(value)] += count
    if F.q == 3:
        # omega^2=-1-omega; Norm(a+b*omega)=a^2-a*b+b^2.
        a = exponents[0]-exponents[2]
        b = exponents[1]-exponents[2]
        return a*a-a*b+b*b
    return (exponents[0]-exponents[1])**2


def rational_character_sum(value_counts,F):
    """Exact sum when its value is rational (as in the plane formula)."""
    exponents = Counter()
    for value,count in value_counts.items():
        exponents[F.char_exponent(value)] += count
    if F.q == 3:
        if exponents[1] != exponents[2]:
            raise AssertionError('Character sum unexpectedly nonrational')
        return exponents[0]-exponents[1]
    return exponents[0]-exponents[1]


def check_mobius():
    counts = Counter()
    for q in (2,3,4):
        for m in range(15):
            for L in range(m+4):
                left = sum((-1)**j*q**(j*(j-1)//2)*gauss(m,j,q) for j in range(L+1))
                right = 1 if m == 0 else (-1)**L*q**(L*(L+1)//2)*gauss(m-1,L,q)
                assert left == right,(q,m,L,left,right)
                counts['partial_mobius_identities'] += 1
                if m >= L+1:
                    assert gauss(m-1,L,q) <= gauss(m,L+1,q)
                    counts['mobius_tail_inequalities'] += 1
        for d in range(13):
            for k in range(d+1):
                for j in range(d-k+1):
                    assert gauss(d,k,q)*gauss(d-k,j,q) == gauss(k+j,k,q)*gauss(d,k+j,q)
                    counts['flag_count_identities'] += 1
    return dict(counts)


def check_uniform_matrix_law():
    counts = Counter()
    for q in (2,3,4):
        for cols in range(11):
            for rows in range(11):
                masses = {}
                u = rows-cols
                for k in range(max(0,-u),cols+1):
                    mass = Fraction(1,q**(k*(k+u)))*g(cols,q)*g(rows,q)/(g(k,q)*g(k+u,q)*g(cols-k,q))
                    masses[k] = mass
                assert sum(masses.values()) == 1,(q,rows,cols)
                counts['rank_law_normalizations'] += 1
                for s in range(cols+1):
                    moment = sum(gauss(k,s,q)*mass for k,mass in masses.items())
                    assert moment == Fraction(gauss(cols,s,q),q**(rows*s)),(q,rows,cols,s)
                    counts['subspace_moment_identities'] += 1
    return dict(counts)


def quadratic_value(coeff,x,pairs,F):
    n = len(x)
    ans = F.dot(coeff[:n],[F.mul(v,v) for v in x])
    for c,(i,j) in zip(coeff[n:],pairs):
        ans = F.add(ans,F.mul(c,F.mul(x[i],x[j])))
    return ans


def check_quadratics():
    cases = []
    for q,n in ((2,2),(2,3),(3,2),(4,2)):
        F = Field(q)
        vectors = list(product(range(q),repeat=n))
        pairs = [(i,j) for i in range(n) for j in range(i+1,n)]
        total = 0
        zero_bias = 0
        by_rank = Counter()
        for coeff in product(range(q),repeat=n+len(pairs)):
            polar = [[0]*n for _ in range(n)]
            for i in range(n):
                polar[i][i] = F.add(coeff[i],coeff[i])
            for c,(i,j) in zip(coeff[n:],pairs):
                polar[i][j] = polar[j][i] = c
            r = rank(polar,F)
            values = Counter(quadratic_value(coeff,x,pairs,F) for x in vectors)
            magnitude_squared = character_norm_squared(values,F)
            assert magnitude_squared in (0,q**(2*n-r)),(q,n,coeff,r,magnitude_squared)
            if any(coeff):
                # Equivalent to |bias| <= q^{-1/2}, with integers only.
                assert q*magnitude_squared <= q**(2*n),(q,n,coeff)
            if r == 0 and any(coeff):
                assert magnitude_squared == 0
                assert set(values.values()) == {q**(n-1)} and len(values) == q
            # A nonzero homogeneous quadratic is never the zero function.
            assert (values.get(0,0) == q**n) == (not any(coeff))
            total += 1
            zero_bias += (magnitude_squared == 0)
            by_rank[r] += 1
        cases.append({'q':q,'variables':n,'quadratics_checked':total,
                      'zero_character_sum_count':zero_bias,'polar_rank_histogram':dict(sorted(by_rank.items()))})
    return cases


def alternating_matrix(coeff,n,pairs,F):
    a = [[0]*n for _ in range(n)]
    for c,(i,j) in zip(coeff,pairs):
        a[i][j] = c
        a[j][i] = F.neg_table[c]
    return a


def wedge_histogram(n,F):
    vectors = list(product(range(F.q),repeat=n))
    pairs = [(i,j) for i in range(n) for j in range(i+1,n)]
    histogram = Counter()
    dependent = 0
    for x in vectors:
        for y in vectors:
            wedge = tuple(F.sub(F.mul(x[i],y[j]),F.mul(x[j],y[i])) for i,j in pairs)
            if any(wedge):
                histogram[wedge] += 1
            else:
                dependent += 1
    assert dependent == (F.q+1)*F.q**n-F.q
    assert sum(histogram.values()) == (F.q**n-1)*(F.q**n-F.q)
    assert set(histogram.values()) == {F.q*(F.q**2-1)}
    return histogram,dependent


def check_alternating_planes():
    out = []
    n = 4
    pairs = [(i,j) for i in range(n) for j in range(i+1,n)]
    for q in (2,3,4):
        F = Field(q)
        histogram,dependent = wedge_histogram(n,F)
        # Exhaustive for every field; wedge aggregation makes this small.
        counts = Counter()
        for coeff in product(range(q),repeat=len(pairs)):
            r = rank(alternating_matrix(coeff,n,pairs,F),F)
            values = Counter()
            for wedge,multiplicity in histogram.items():
                values[F.dot(coeff,wedge)] += multiplicity
            char_sum = rational_character_sum(values,F)
            expected = q**(2*n-r)-(q+1)*q**n+q
            assert char_sum == expected,(q,coeff,r,char_sum,expected)
            counts[r] += 1
        total = q**len(pairs)
        expected_nonsingular = Fraction(total)
        for j in range(1,n//2+1):
            expected_nonsingular *= 1-Fraction(1,q**(2*j-1))
        assert expected_nonsingular.denominator == 1
        assert counts[n] == expected_nonsingular
        out.append({'q':q,'variables':n,'forms_checked':total,
                    'independent_ordered_pairs':sum(histogram.values()),
                    'dependent_ordered_pairs':dependent,
                    'distinct_nonzero_decomposable_bivectors':len(histogram),
                    'rank_histogram':dict(sorted(counts.items())),
                    'nonsingular_count':counts[n],
                    'nonsingular_probability':str(Fraction(counts[n],total))})
    # Also verify the n=0,2 endpoint cases of the nonsingularity product.
    endpoint_checks = 0
    for q in (2,3,4):
        F = Field(q)
        for n in (0,2):
            pairs = [(i,j) for i in range(n) for j in range(i+1,n)]
            nonsingular = sum(rank(alternating_matrix(c,n,pairs,F),F)==n
                              for c in product(range(q),repeat=len(pairs)))
            expected = Fraction(q**len(pairs))
            for j in range(1,n//2+1):
                expected *= 1-Fraction(1,q**(2*j-1))
            assert nonsingular == expected
            endpoint_checks += 1
    return {'four_dimensional_cases':out,'additional_nonsingular_product_checks':endpoint_checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results'/'exact_checks.json')
    args = parser.parse_args()
    result = {'status':'PASS',
              'scope':'Exact finite identities only. These computations do not establish the asymptotic theorems.',
              'fields':{'2':'prime field','3':'prime field','4':'F_2[z]/(z^2+z+1)'},
              'mobius_and_flags':check_mobius(),
              'uniform_matrix_law':check_uniform_matrix_law(),
              'quadratic_fourier':check_quadratics(),
              'alternating_plane_fourier':check_alternating_planes()}
    result['totals'] = {
        'quadratic_forms':sum(c['quadratics_checked'] for c in result['quadratic_fourier']),
        'alternating_forms':sum(c['forms_checked'] for c in result['alternating_plane_fourier']['four_dimensional_cases']),
        'mobius_identities':result['mobius_and_flags']['partial_mobius_identities'],
        'flag_identities':result['mobius_and_flags']['flag_count_identities'],
        'uniform_matrix_moments':result['uniform_matrix_law']['subspace_moment_identities']}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'output':str(args.output),'totals':result['totals']},indent=2))


if __name__ == '__main__':
    main()
