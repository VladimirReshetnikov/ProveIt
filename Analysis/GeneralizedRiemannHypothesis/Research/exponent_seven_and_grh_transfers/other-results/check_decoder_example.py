"""Exact sufficient bounds for the worked high-band example, requiring only Python 3.

Checks a theorem about every genuine band with the promised parameters and
observation budget. The script does not generate or take as input L-function zeros.
"""
from fractions import Fraction as Q
from math import isqrt


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def divisors(n):
    values = set()
    for k in range(1, isqrt(n) + 1):
        if n % k == 0:
            values.update((k, n // k))
    return sorted(values)


def kernel_bound(radius, height):
    assert radius * height >= 1
    prefactor = Q(2 * 16**8, 7) / (radius**7 * height**8)
    return prefactor * (108 * height**2 + 40 * height / radius
                        + 6 / radius**2 + Q(1, 4))


height = 10**12
prime_d = 46199
witness = 110881
uncertainty = Q(1, 10**7)
assert is_prime(prime_d) and is_prime(witness)
moduli = [q for q in divisors(2 * (prime_d + 1))
          if q % 18480 == 0 and prime_d % q == q // 2 - 1]
assert moduli == [18480, 92400]
assert pow(witness, (prime_d - 1) // 2, prime_d) == prime_d - 1
assert [(witness - 1) % q == 0 for q in moduli] == [True, False]
# e > 8/3, so log(d) < 12.
assert Q(8, 3)**12 > prime_d

# At zero use r=1/8, hence 2r<log 2 and cosh(r)<2.
origin_kernel = kernel_bound(Q(1, 8), height)
origin_density = Q(1024, 7 * height)
point_error = origin_density + uncertainty + (9 * 12 + 60) * origin_kernel
assert 9 * origin_kernel < Q(1, 2)
# Endpoints of the inverted log(d) interval differ from the true log(d)
# by at most twice point_error divided by (1-9K).
log_radius = 4 * point_error
assert log_radius < Q(1, prime_d + 1)  # smaller than the distance to each neighbor
print("Origin certificate isolates d = 46199")
print("Admissible moduli:", moduli)

# At u=log(p) choose r=1/(4p), so 2r<log(1+1/p).
# cosh((u+2r)/2) <= 2p follows from exp(r)<2 and sqrt(p)<=p.
radius = Q(1, 4 * witness)
prime_kernel = kernel_bound(radius, height)
prime_density = Q(1024 * witness, 7 * height)
point_error = prime_density + uncertainty + (9 * 12 + 60) * prime_kernel
# The positive mass is 2 log(p)/sqrt(p) > 2/334.
assert witness < 334**2 and 2 * point_error < Q(2, 334)
print("Prime witness 110881 separates the two moduli")
print("All inequalities verified with rational arithmetic")
