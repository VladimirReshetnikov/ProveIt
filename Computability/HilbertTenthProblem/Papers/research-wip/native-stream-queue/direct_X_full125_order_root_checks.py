"""Fresh modular-order cut only; no repository or predecessor is loaded."""
import json
import math


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def cube_base_power(exponent, modulus):
    accumulator = 1
    for digit in format(exponent, 'b'):
        accumulator = (accumulator * accumulator) % modulus
        if digit == '1':
            accumulator = (accumulator + accumulator + accumulator) % modulus
    return accumulator


factorization = [(2, 3), (3, 2), (5, 3), (41, 2), (107, 1),
                 (10223, 1), (184711, 1), (842887, 1)]
order = math.prod(prime ** multiplicity for prime, multiplicity in factorization)
modulus = (1 << 125) - 1
require(order == 2576525686996852656333000, 'order factorization')
require(math.gcd(3, modulus) == 1, 'unit base')

# An independently built prime sieve supplies every possible small divisor.
limit = math.isqrt(max(prime for prime, _ in factorization))
is_prime = [True] * (limit + 1)
is_prime[0] = is_prime[1] = False
for candidate in range(2, math.isqrt(limit) + 1):
    if is_prime[candidate]:
        for composite in range(candidate * candidate, limit + 1, candidate):
            is_prime[composite] = False
small_primes = [index for index, yes in enumerate(is_prime) if yes]
prime_checks = []
for prime, _ in factorization:
    divisors = [divisor for divisor in small_primes
                if divisor * divisor <= prime]
    require(all(prime % divisor for divisor in divisors), 'order factor prime')
    prime_checks.append({'prime': prime, 'trial_divisors': len(divisors)})

full_residue = cube_base_power(order, modulus)
require(full_residue == 1, 'full order power')
proper = []
for prime, _ in factorization:
    exponent = order // prime
    residue = cube_base_power(exponent, modulus)
    require(residue != 1, 'proper prime quotient')
    proper.append({'prime': prime, 'exponent': exponent, 'residue': residue})

endpoint = 5 ** 34
next_endpoint = 5 ** 35
margin = 11 * order - (11 + 28 * endpoint)
require(margin >= 0, 'range endpoint')
require(2 * order < 3 * next_endpoint, 'partial-test boundary')
require(125 == 5 ** 3, 'radix level')
print(json.dumps({
    'modulus': modulus,
    'order': order,
    'factorization': factorization,
    'order_factors_prime': prime_checks,
    'prime_sieve_limit': limit,
    'full_order_residue': full_residue,
    'proper_order_tests': proper,
    'largest_d_from_inequality': (11 * order - 11) // 28,
    'last_exponent': endpoint,
    'last_exponent_n': 34,
    'positive_margin': margin,
    'next_exponent': next_endpoint,
    'next_exponent_n': 35,
    'partial_test_2O_below_3d': True,
    'scope': 'Original finite modular cut; no compiler/source evaluation or modulus primality claim',
}, indent=2, sort_keys=True))
