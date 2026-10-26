#!/usr/bin/env python3
"""Recompute the finite data; universal exponent claims are proved in Lean."""
from math import gcd, prod
import json

primes = (47, 2011, 120199)
kernel_residues = (26, 1995, 114787)
modulus = prod(primes)
kernel = sum(r * (modulus // p) * pow(modulus // p, -1, p)
             for p, r in zip(primes, kernel_residues)) % modulus
base = pow(2, 94517, modulus)
radix = pow(2, 47, modulus)
gamma = (pow(radix, 977, modulus) * (base * base - 1)
         * (1 + base * (kernel + base))) % modulus

assert modulus == 11360848883
assert (base, radix, kernel, gamma) == (
    10287028452, 10653241607, 1491904576, 706142772)
assert pow(base, 120199, modulus) == base
assert gcd(gamma, modulus) == 1
assert -567596732 * gamma + 35279435 * modulus == 1

examples = []
for rw, n in ((0, 0), (1, 0), (0, 1), (2, 3), (17, 0)):
    q = pow(base, 120199 ** n, modulus)
    width_power = pow(base, 120199 ** rw, modulus)
    residue = (pow(radix, 977, modulus) * (q * q - 1)
               * (1 + q * (kernel + width_power))) % modulus
    assert residue == gamma
    examples.append({"rw": rw, "n": n, "gamma_mod_radical": residue})

print(json.dumps({
    "radical": modulus,
    "base_mod_radical": base,
    "radix_mod_radical": radix,
    "kernel_mod_radical": kernel,
    "gamma_mod_radical": gamma,
    "gamma_mod_prime_factors": dict(zip(map(str, primes),
                                        (gamma % p for p in primes))),
    "bezout_gamma": -567596732,
    "bezout_radical": 35279435,
    "base_fixed_point": pow(base, 120199, modulus),
    "examples": examples,
    "scope": "Finite arithmetic cross-check; universal proof is in GammaCertificate.lean"
}, indent=2))
