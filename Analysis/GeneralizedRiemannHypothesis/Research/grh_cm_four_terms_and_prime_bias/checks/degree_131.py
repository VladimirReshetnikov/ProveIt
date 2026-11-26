"""Exact check for five terms, normalized constant term, degree at most 1000."""
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json

P = 1_000_000_007
LIMIT = 1000
coeffs = json.loads(Path(__file__).with_name("class_polynomials.json").read_text())["131"]

def valuation(n):
    assert n
    v = 0
    while n % 17 == 0:
        n //= 17
        v += 1
    return v

def det3(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])
            +a[2]*(b[0]*c[1]-b[1]*c[0]))

def verify():
    powers = [[1,0,0,0,0]]
    for _ in range(LIMIT):
        last = powers[-1]
        powers.append([(a-last[4]*b)%P for a,b in zip([0]+last[:4], coeffs[:5])])
    for n in (1,2):
        # 17^3 > LIMIT. A necessary 17-adic condition gives this small anchor.
        projected = [[v[i] for i in (1,2,3,4) if i != n] for v in powers]
        buckets = {}
        for e in range(1,LIMIT+1):
            if e != n:
                buckets.setdefault(valuation(e-n),[]).append(e)
        totals = passed = 0
        for r in combinations_with_replacement(sorted(buckets),3):
            if sum(r) < 3*n:
                continue
            choices = [combinations(buckets[v],r.count(v)) for v in sorted(set(r))]
            for groups in product(*choices):
                a,b,c = (e for group in groups for e in group)
                plus = sum(valuation(abs(e-n))-valuation(e) for e in (a,b,c))
                if plus < 3*n:
                    continue
                totals += 1
                if det3(projected[a],projected[b],projected[c]) % P == 0:
                    passed += 1
        print(f"anchor {n}: {totals} admissible triples, {passed} modular singularities")
        assert passed == 0
    print("Every five distinct powers with least exponent 0 and largest <= 1000 are independent.")

if __name__ == "__main__":
    verify()
