"""Certified integer L1 lower bounds from residues and an exact coordinate sum.

Auxiliary moduli concern integer Euler characteristics, not the coefficient
field of the Khovanov complex. Every function uses exact integer arithmetic.
"""
from math import gcd, isqrt


def validate_primes(primes, check=None):
    """Return distinct odd primes in the prototype's signed 31-bit range."""
    result = tuple(primes)
    if not result or len(set(result)) != len(result):
        raise ValueError("supply a nonempty sequence of distinct odd primes")
    for p in result:
        if check is not None:
            check()
        if type(p) is not int or p < 3 or p >= (1 << 31) or p % 2 == 0:
            raise ValueError("auxiliary primes must be odd integers below 2^31")
        for divisor in range(3, isqrt(p) + 1, 2):
            if check is not None:
                check()
            if p % divisor == 0:
                raise ValueError("an auxiliary modulus is composite")
    return result


def balanced(residue, modulus):
    if type(modulus) is not int or modulus < 3 or modulus % 2 == 0:
        raise ValueError("balanced representatives require an odd modulus >= 3")
    value = residue % modulus
    return value - modulus if 2 * value > modulus else value


def crt_vector(old, modulus, new, prime):
    """Merge two residue vectors with coprime moduli; return canonical residues."""
    if len(old) != len(new) or gcd(modulus, prime) != 1:
        raise ValueError("CRT vectors need equal lengths and coprime moduli")
    inverse = pow(modulus, -1, prime)
    return tuple(x + modulus * (((y - x) * inverse) % prime)
                 for x, y in zip(old, new))


def minimum_l1_lift(residues, modulus, exact_sum=None):
    """Minimum L1 of integer lifts, optionally subject to their exact sum.

    Returns both the minimum and an attaining lift. The latter is a witness
    for the small lattice minimization, not for a completed knot complex.
    """
    lift = [balanced(x, modulus) for x in residues]
    if exact_sum is None:
        return sum(map(abs, lift)), tuple(lift)
    difference = exact_sum - sum(lift)
    if difference % modulus:
        raise ValueError("exact sum is incompatible with the residues")
    steps = difference // modulus
    if not steps:
        return sum(map(abs, lift)), tuple(lift)
    if not lift:
        raise ValueError("an empty vector cannot have nonzero sum")
    direction = 1 if steps > 0 else -1
    remaining = abs(steps)
    discounts = sorted((i for i, b in enumerate(lift) if b * direction < 0),
                       key=lambda i: -abs(lift[i]))
    for i in discounts[:remaining]:
        lift[i] += direction * modulus
        remaining -= 1
    if remaining:
        # Every unused marginal cost is now exactly modulus. If there was
        # a discount, its coordinate already has the required sign.
        index = discounts[0] if discounts else 0
        lift[index] += direction * modulus * remaining
    return sum(map(abs, lift)), tuple(lift)


def threshold_is_exact(modulus, coordinate_bounds, multiplicities, threshold=1,
                       *, exact_sums=True):
    """A sufficient deterministic completion criterion, not stabilization."""
    if type(threshold) is not int or threshold < 0:
        raise ValueError("threshold must be a nonnegative integer")
    if len(coordinate_bounds) != len(multiplicities):
        raise ValueError("bound and multiplicity lengths differ")
    divisor = 2 if exact_sums else 1
    for bound, weight in zip(coordinate_bounds, multiplicities):
        if type(bound) is not int or bound < 0 or type(weight) is not int or weight < 1:
            raise ValueError("coordinate bounds must be nonnegative and weights positive")
        if modulus <= bound + threshold // (divisor * weight):
            return False
    return True
