"""Verify Mills constant enclosures using only integer arithmetic and Python 3."""
import json
from functools import cache
from math import gcd, isqrt
from pathlib import Path

DATA = json.loads(Path(__file__).with_name("mills_data.json").read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


@cache
def prove_prime(p):
    if p < 10000:
        require(p >= 2 and all(p % d for d in range(2, isqrt(p) + 1)), "small prime")
        return
    factors = DATA["proofs"][str(p)]
    known = 1
    used = set()
    for prime, exponent, witness in factors:
        q = int(prime)
        require(1 < q < p and exponent >= 1 and q not in used, "factor input")
        prove_prime(q)
        used.add(q)
        known *= q ** exponent
        require(pow(witness, p - 1, p) == 1, "Fermat congruence")
        require(gcd(pow(witness, (p - 1) // q, p) - 1, p) == 1, "order witness")
    require((p - 1) % known == 0 and known * known > p, "Pocklington criterion")


def provably_nonprime(n):
    """An actual failing strong probable-prime test certifies compositeness."""
    if n < 2 or n % 2 == 0:
        return n != 2
    odd = n - 1
    while odd % 2 == 0:
        odd //= 2
    twos = ((n - 1) // odd).bit_length() - 1
    for base in range(2, min(n, 1000)):
        value = pow(base, odd, n)
        if value == 1 or value == n - 1:
            continue
        for _ in range(twos - 1):
            value = value * value % n
            if value == n - 1:
                break
        else:
            return True
    return False


def floor_root(n, degree):
    """Integer Newton iteration from a certified upper bound."""
    x = 1 << ((n.bit_length() + degree - 1) // degree)
    while True:
        y = ((degree - 1) * x + n // x ** (degree - 1)) // degree
        if y >= x:
            require(x ** degree <= n < (x + 1) ** degree, "root bound")
            return x
        x = y


def digits_from_cell(prime, level, m, d):
    precision = 66
    scale = 10 ** precision
    low, high = prime * scale, (prime + 1) * scale
    for _ in range(level):
        low = floor_root(low ** d * scale ** (m - d), m)
        high = 1 + floor_root(high ** d * scale ** (m - d), m)
    prefix = ""
    for a, b in zip(str(low), str(high)):
        if a != b:
            break
        prefix += a
    require(len(str(low)) == len(str(high)) == precision + 1, "format")
    return prefix[0] + "." + prefix[1:]


def verify(case):
    m, d, B = (case[key] for key in ["numerator", "denominator", "threshold"])
    # B(m-2d)/2d is positive; log(10) is between 2 and 3.
    require(m > 2*d and B * (m - 2*d) > d, "monotonicity of tail ratio")
    require(10 ** (B * (m - 2*d)) > (3 * B) ** (2*d), "tail threshold")
    anchor, anchor_level = 1, 0
    last = None
    for n, row in enumerate(case["rows"], 1):
        p, f = int(row["prime"]), int(row["floor"])
        distance = n - anchor_level
        numerator, denominator = m ** distance, d ** distance
        left = anchor ** numerator
        require(f ** denominator <= left < (f + 1) ** denominator, "floor")
        prove_prime(p)
        if n <= 7:
            require(row["mode"] == "least" and p >= f, "prefix")
            require(all(provably_nonprime(i) for i in range(f, p)), "skipped prime")
        else:
            require(row["mode"] == "bridge" and p > f, "bridge cell")
        if last is not None:
            require((p + 1) ** d < (last + 1) ** m, "upper inclusion")
        if p ** denominator >= left:
            anchor, anchor_level = p, n
        if n == 7:
            require(anchor_level == n, "prefix ends with a complete cell")
            prefix = digits_from_cell(p, n, m, d)
        last = p
    require(n >= 7 and anchor_level == n and last >= 10 ** B, "tail entry")
    digits = len(str(last))
    print(f"{m}/{d}  levels={n}  tail prime digits={digits}  minimum={prefix}...")


if __name__ == "__main__":
    expected = [(9, 4), (11, 5), (21, 10), (41, 20), (201, 100)]
    require([(c["numerator"], c["denominator"]) for c in DATA["cases"]] == expected,
            "incomplete case list")
    for case in DATA["cases"]:
        verify(case)
