"""Generate divisor covers. The independent verifier needs no factoring software."""
import json
from pathlib import Path
from math import gcd
from sympy import factorint, primerange, sqrt_mod

LIMIT = 10**11
small_primes = list(primerange(2, 251))
covers = []
for q in primerange(2, 116**2 + 1):
    value = q**6 + q**3 + 1
    factors = []
    for divisor, exponent in factorint(value).items():
        d = int(divisor)
        entry = [d, int(exponent)]
        if d > LIMIT:
            for w in small_primes:
                if gcd(d, w*(w*w+w+1)*(w**6+w**3+1)) != 1:
                    continue
                root = sqrt_mod(w, d)
                if root is not None:
                    entry.extend([w, int(root)])
                    break
            else:
                raise ArithmeticError(f"missing witness for {d}")
        factors.append(entry)
    covers.append([q, sorted(factors)])
Path(__file__).with_name("large_certificate.json").write_text(json.dumps(covers, separators=(",", ":")) + "\n")
