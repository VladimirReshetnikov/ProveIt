"""Cross-check the pair calculation on a fixed reproducible sample (SymPy and NumPy).

Usage: python crosscheck_ratios.py path/to/directory/containing/ratio_norms.py
The independent side enumerates signed factor pairs of 4*(i^2*q^7-j^2*p^7),
tests both original norm equations, and uses Euler's criterion for witnesses.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from hashlib import sha256
from math import gcd
from pathlib import Path
from random import Random
import sys

from sympy import divisors, primerange


def audit_pair(i, j, p, q, witnesses, floor):
    signed = 4 * (i*i * q**7 - j*j * p**7)
    solutions = set()
    for raw in divisors(abs(signed)):
        plus = int(raw)
        minus = signed // plus
        if plus < abs(minus):
            continue
        # plus = i*b+j*a, minus = i*b-j*a. Either sign of minus is possible.
        a, left_rem = divmod(plus - minus, 2 * j)
        b, right_rem = divmod(plus + minus, 2 * i)
        if left_rem or right_rem:
            continue
        m, rem = divmod(4 * p**7 - a*a, i*i)
        if rem or m <= floor or b*b + j*j*m != 4*q**7:
            continue
        first = next((r for r in witnesses if pow((-m) % r, (r-1)//2, r) == 1), 0)
        assert first > 0, (i, j, p, q, a, b, m)
        solutions.add((a, b, m, first))
    return solutions


@lru_cache(maxsize=None)
def local_residues(prime, k, factor, p_res):
    """Enumerate all origins x and c for M=x*c^2, using full local unit conditions."""
    modulus = prime**k
    squares = {t*t % modulus for t in range(modulus)}
    if prime == 2:
        origins = range(3, modulus, 8)
    else:
        origins = (x for x in range(modulus)
                   if pow((-x) % prime, (prime-1)//2, prime) == prime-1)
    represented = {x*s % modulus for x in origins for s in squares}
    return {m for m in represented if (4*pow(p_res, 7, modulus)-factor*factor*m) % modulus in squares}


def direct_locally_eligible(i, j, p, q, floor, moduli):
    if p == q or 4*p**7 <= floor*i*i or 4*q**7 <= floor*j*j:
        return False
    for r, k in moduli:
        modulus = r**k
        one = local_residues(r, k, i, p % modulus)
        two = local_residues(r, k, j, q % modulus)
        if one.isdisjoint(two):
            return False
    return True


def run(production):
    floor = 31 * 10**19
    primes = [int(p) for p in primerange(2, 4201) if 4*p**7 > floor]
    witnesses = [int(r) for r in primerange(13, 701) if 4*r**7 < floor]
    moduli = [(2,7), (3,4), (5,3), (7,2), (11,2), (13,1), (17,1), (19,1), (23,1)]
    assert primes == production.PRIMES and witnesses == [r for r,_ in production.WITNESSES]
    assert moduli == production.MODULI
    rng = Random(19790317)
    samples = defaultdict(set)
    for j in range(2, 13):
        for i in range(1, j):
            if gcd(i,j) != 1:
                continue
            while len(samples[i,j]) < 28:
                samples[i,j].add(tuple(rng.sample(primes, 2)))
    # Include additional actual production jobs in each ratio across the prime range.
    # Random representatives of each block enter an independent reservoir.
    streamed = Counter()
    passing = defaultdict(list)
    for i, j, chunk in production.jobs():
        cell = (i,j)
        p, q = rng.choice(chunk)
        streamed[cell] += 1
        reservoir = passing[cell]
        if len(reservoir) < 12:
            reservoir.append((p,q))
        else:
            index = rng.randrange(streamed[cell])
            if index < len(reservoir):
                reservoir[index] = (p,q)
    for cell, extra in passing.items():
        samples[cell].update(extra)

    # Query the production job stream on exactly our sampled keys to verify
    # membership of the independent full-residue eligibility test.
    listed = defaultdict(set)
    for i, j, chunk in production.jobs():
        listed[i,j].update(samples[i,j].intersection(chunk))
    counts = Counter()
    digest = sha256()
    for (i, j), sample in sorted(samples.items()):
        for p, q in sorted(sample):
            eligible = direct_locally_eligible(i, j, p, q, floor, moduli)
            assert eligible == ((p,q) in listed[i,j]), (i,j,p,q,"local")
            answers = audit_pair(i,j,p,q,witnesses,floor)
            _, _, (one, number, largest) = production.check((i,j,[(p,q)]))
            max_witness = max((w for *_, w in answers),default=0)
            assert (one, number, largest) == (1,len(answers),max_witness), (i,j,p,q,"factor")
            d = i*i*q**7-j*j*p**7
            counts["sampled"] += 1
            counts["positive" if d > 0 else "negative"] += 1
            counts["locally_eligible"] += int(eligible)
            counts["solutions"] += len(answers)
            counts["eligible_solutions"] += len(answers) * int(eligible)
            counts["solution_pairs"] += bool(answers)
            counts["max_witness"] = max(counts["max_witness"], max_witness)
            digest.update(f"{i},{j},{p},{q},{int(eligible)},{sorted(answers)}\n".encode())
    print("Rational-norm cross-check against the production code")
    print("ratios",len(samples))
    for key in ("sampled","positive","negative","locally_eligible","solutions",
                "eligible_solutions","solution_pairs","max_witness"):
        print(key,counts[key])
    print("per-pair agreement on candidate count and largest first witness; local eligibility agreement")
    print("canonical sorted record SHA-256",digest.hexdigest())


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Supply the directory containing ratio_norms.py")
    sys.path.insert(0,str(Path(sys.argv[1]).resolve()))
    import ratio_norms
    run(ratio_norms)
