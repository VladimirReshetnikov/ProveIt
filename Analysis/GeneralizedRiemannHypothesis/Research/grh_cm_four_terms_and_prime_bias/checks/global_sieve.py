"""Exhaust the four-term CM problem, using the three analytic cutoffs in the text."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
from math import gcd, isqrt, prod

from local_disks import verify
from verify_class_polynomials import forms, singular_j, S

A, B, C = 4*7**6, 4*13**6, 4*91**4


def remaining_discriminants():
    """Disjoint ranges after applying the two-prime theorem."""
    yield from range(3, A)
    yield from range((A+48)//49*49, B, 49)
    yield from range((B+8280)//8281*8281, C, 8281)


def separated(d, a, b):
    return a == 0 or (d >= 16*a*a and 9*d*(b-a)**2 >= 16*a*a*b*b)


@lru_cache(None)
def middle_coefficients(a, residue):
    return [b for b in range(a+1) if (b*b+residue) % (4*a) == 0]


def integer_separation(d):
    count = last = 0
    for a in range(1, min(151, isqrt(d//3))+1):
        if not separated(d, last, a):
            continue
        for b in middle_coefficients(a, d % (4*a)):
            c = (b*b+d)//(4*a)
            if c >= a and gcd(gcd(a,b),c) == 1:
                count += 1
                last = a
                break
        if count == 4:
            return True
    return False


def interval_determinant(d, reduced_forms):
    radii = []
    for a,b,_ in reduced_forms:
        if b < 0:
            continue  # conjugate values have identical radii
        real, imag = singular_j(d,a,b)
        squared = real*real + imag*imag
        radii.append((isqrt(max(0, squared.lo)*S), isqrt(squared.hi*S)+1))
    for rows in combinations(sorted(radii),4):
        if any(rows[i][1] >= rows[i+1][0] for i in range(3)):
            continue
        diagonal = prod(lo**i for i,(lo,hi) in enumerate(rows))
        error = sum(prod(rows[i][1]**perm[i] for i in range(4))
                    for perm in permutations(range(4)) if perm != (0,1,2,3))
        if error < diagonal:
            return True
    return False


def main():
    local_table = verify()
    for bound, leading in [(A, [1,7,49,343]), (B,[1,13,169,2197]), (C,[1,49,169,8281])]:
        assert bound >= 4*leading[-1]**2
        assert all(separated(bound,a,b) for a,b in zip(leading,leading[1:]))
    counts = Counter()
    for d in remaining_discriminants():
        if d % 4 not in (0,3):
            continue
        if any(d % (p*p) and pow(-d,(p-1)//2,p) != 1 for p in (7,13)):
            result = 'supersingular reduction'
        elif integer_separation(d):
            result = 'integer separation'
        else:
            reduced = list(forms(d))
            if len(reduced) < 4:
                result = 'degree below four'
            elif d in local_table:
                result = 'class polynomial disk'
            else:
                assert interval_determinant(d, reduced), d
                result = 'complex determinant'
            print(f'{d:5}  h={len(reduced):2}  {result}')
        counts[result] += 1
    print('Cutoffs:', A, B, C)
    print('Discriminants in finite ranges:', sum(counts.values()))
    for label,count in counts.items():
        print(f'{label}: {count}')


if __name__ == '__main__':
    main()
