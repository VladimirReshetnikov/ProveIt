"""Exhaust five leading coefficients after the five normal-form cutoffs."""
from collections import Counter
from functools import lru_cache
from math import gcd, isqrt

# Each type records the primes 7 and 13 dividing the conductor.
# If both divide the conductor, also record whether 19 divides it.
LEADING = {
    (): [1, 7, 13, 49, 91],
    (7,): [1, 13, 49, 169, 637],
    (13,): [1, 7, 49, 169, 343],
    (7, 13): [1, 19, 49, 169, 361],
    (7, 13, 19): [1, 49, 169, 361, 8281],
}


def separated(d, a, b):
    return a == 0 or (d >= 16*a*a and 9*d*(b-a)**2 >= 16*a*a*b*b)


def conductor_type(d):
    ps = tuple(p for p in (7, 13) if d % (p*p) == 0)
    return (7, 13, 19) if ps == (7, 13) and d % (19*19) == 0 else ps


@lru_cache(None)
def middle_coefficients(a, residue):
    return [b for b in range(a+1) if (b*b+residue) % (4*a) == 0]


def five_coefficients(d):
    count = last = 0
    for a in range(1, min(251, isqrt(d//3))+1):
        if not separated(d, last, a):
            continue
        for b in middle_coefficients(a, d % (4*a)):
            c = (b*b+d)//(4*a)
            if c >= a and gcd(gcd(a, b), c) == 1:
                count += 1
                last = a
                break
        if count == 5:
            return True
    return False


def census(verbose=True):
    survivors = []
    for kind, values in LEADING.items():
        step = 1
        for p in kind:
            step *= p*p
        upper = max(4*values[-1]**2, 16*values[-2]**2)
        assert all(separated(upper, a, b) for a,b in zip(values, values[1:]))
        counts = Counter()
        for d in range(step, upper, step):
            if d < 3 or d % 4 not in [0, 3] or conductor_type(d) != kind:
                continue
            local_primes = [p for p in (7, 13) if p not in kind]
            if kind == (7, 13):
                local_primes.append(19)
            if any(pow(-d, (p-1)//2, p) != 1 for p in local_primes):
                counts['local'] += 1
            elif five_coefficients(d):
                counts['arch'] += 1
            else:
                counts['left'] += 1
                survivors.append(d)
        if verbose:
            print(kind, upper, sum(counts.values()), dict(counts))
    survivors.sort()
    assert len(survivors) == len(set(survivors))
    if verbose:
        print('Remaining', len(survivors))
        print(' '.join(map(str, survivors)))
    return survivors



def reduced_class_number(d):
    total = 0
    for a in range(1, isqrt(d//3)+1):
        for b in middle_coefficients(a, d % (4*a)):
            c = (b*b+d)//(4*a)
            if c >= a and gcd(gcd(a,b), c) == 1:
                total += 1 if b in (0, a) or a == c else 2
    return total


def additional_prime(d, h):
    # For p=1 mod 3 all supersingular j are nonzero.
    for p in (7, 13, 19, 31, 37, 43):
        num_ss = p//12 + int(p % 12 == 7)
        if h > 4*num_ss and pow(-d, (p-1)//2, p) == p-1:
            return p
    return None


def reduce_survivors(survivors):
    rest = []
    counts = Counter()
    for d in survivors:
        h = reduced_class_number(d)
        if h < 5:
            counts['degree below five'] += 1
        elif h == 5:
            counts['degree-five census'] += 1
        elif additional_prime(d, h):
            counts['further supersingular prime'] += 1
        else:
            rest.append(d)
    print('Additional census', dict(counts))
    print('Final list', len(rest))
    print(' '.join(map(str,rest)))
    return rest

if __name__ == '__main__':
    reduce_survivors(census())
