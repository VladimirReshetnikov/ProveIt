#!/usr/bin/env python3
"""An independent exact counterexample certificate; no imports required."""
a = 3 * 2**99 + 1
assert a == 1901475900342344102245054808065
for b, s, expected_digit in [(2, 100, 4), (3, 102, 5)]:
    modulus = 10**(s + 1)
    residue = (pow(a, 10**(b + 1), modulus)
               - pow(a, 10**b, modulus)) % modulus
    assert residue == expected_digit * 10**s
assert 102 - 100 == 2
print("Counterexample verified exactly: S(2)=100, S(3)=102, D(3)=2.")
