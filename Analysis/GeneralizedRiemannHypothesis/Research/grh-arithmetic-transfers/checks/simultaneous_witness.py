"""Check one A4 sextic for all 66 candidate primes using integer arithmetic."""
import argparse
from math import gcd
from pathlib import Path
import sys
sys.dont_write_bytecode = True

from isogeny_sieve import P, crt_parameter, irreducible, prime_list, splits, survives

BASE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-parameter", action="store_true")
    args = parser.parse_args()
    primes = prime_list(P)
    candidates = [p for p in primes if p % 4 == 3 and survives(p, primes)]
    targets = set()
    for p in candidates:
        for q in primes:
            if 4*q >= p:
                break
            if splits(q, p):
                targets.add(q)
                assert 4*q**3 >= p
    targets = sorted(targets)

    r = 9343
    assert r in primes and r not in targets
    roots = [x for x in range(r) if (x**3 - 3*x - 1) % r == 0]
    assert roots == [755, 8688, 9243]
    x = roots[0]
    base_value = x**3 - 3*x - 1
    assert base_value % r == 0 and base_value % (r*r) != 0

    parameter_file = BASE / "simultaneous_parameter.txt"
    if args.write_parameter:
        a, b = crt_parameter(targets, split_prime=r)
        parameter_file.write_text(f"{a}\n{b}\n")
    else:
        a, b = map(int, parameter_file.read_text().split())
    assert gcd(a, b) == 1 and a % (r*r) == 0 and b % r
    assert all(irreducible(a * pow(b, -1, q) % q, q) for q in targets)
    print("candidate primes", len(candidates), "largest", max(candidates))
    print("union of inertness prescriptions", len(targets), "smallest", targets[0],
          "largest", targets[-1])
    print("auxiliary split prime", r, "roots", roots)
    print("valuation of the norm of alpha - 755 at 9343 is 1")
    print("primitive cubic largest absolute coefficient decimal digits",
          max(len(str(abs(v))) for v in (b, a, a+3*b)))
    print("monic cubic for B*alpha largest absolute coefficient decimal digits",
          max(len(str(abs(v))) for v in (a, b*(a+3*b), b**3)))
    print("all checks passed")


if __name__ == "__main__":
    main()
