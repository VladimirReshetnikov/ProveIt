"""Check the high-range proof with integer multiplication, gcd, and square roots mod d."""
import json
from fractions import Fraction
from math import gcd, isqrt, factorial
from pathlib import Path

LIMIT = 10**11

def primes_to(x):
    return [n for n in range(2, x+1) if all(n % k for k in range(2, isqrt(n)+1))]

def exp_lower(x, terms):
    return sum(x**i / factorial(i) for i in range(terms))

def run():
    assert exp_lower(Fraction(254,10), 70) > LIMIT   # log(10^11)<25.4
    assert Fraction(11,4)**25 < LIMIT                             # e^25<10^11
    a, b = Fraction(1881,1000), Fraction(618,100)
    assert a*Fraction(254,10)+b < 54 and 4*54**6 < LIMIT
    assert a*58+b < 116 and exp_lower(Fraction(58), 100) > 116**12+116**6+1
    assert 116**4+116**2+1 < LIMIT
    rows = json.loads(Path(__file__).with_name("large_certificate.json").read_text())
    assert [q for q,_ in rows] == primes_to(116**2)
    test_primes = set(primes_to(250))
    big = set()
    max_witness = 0
    for q, factors in rows:
        product = 1
        for d, e, *extra in factors:
            assert d > 1 and e >= 1
            product *= d**e
            if d <= LIMIT:
                assert not extra
            else:
                w, root = extra
                assert w in test_primes and 4*w**3 < LIMIT
                assert (root*root - w) % d == 0
                assert gcd(d, w*(w*w+w+1)*(w**6+w**3+1)) == 1
                big.add(d)
                max_witness = max(max_witness, w)
        assert product == q**6+q**3+1
    print(f"Verified {len(rows)} factorizations, {len(big)} distinct large divisors.")
    print(f"Largest auxiliary prime {max_witness}. Coverage: every p > {LIMIT}.")
if __name__ == "__main__":
    run()
