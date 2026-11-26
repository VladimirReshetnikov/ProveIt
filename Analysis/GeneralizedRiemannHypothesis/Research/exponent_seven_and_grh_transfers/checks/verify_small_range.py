"""Check ALL negative quadratic order discriminants |D| <= 118843 for exponent 7.

Primitive reduced positive forms satisfy |b| <= a <= c, b >= 0 on
boundary ties. We count them in one pass over a,b,c, then test every
order with nontrivial class number a power of 7. Python standard library.
"""
from array import array
from math import gcd, isqrt
from check_class_groups import ABS_DISCRIMINANTS, reduced_forms, class_power

LIMIT = 118843


def run():
    counts = array("I", [0]) * (LIMIT + 1)
    for a in range(1, isqrt(LIMIT // 3) + 1):
        for b in range(0, a + 1):
            common = gcd(a,b)
            stop = (LIMIT+b*b)//(4*a)
            for c in range(a, stop+1):
                if gcd(common,c) != 1:
                    continue
                # Both signs give reduced forms off the boundary when b != 0.
                counts[4*a*c-b*b] += 1 + int(0 < b < a < c)
    tested = []
    hits = []
    for abs_d, h in enumerate(counts):
        if h < 7:
            continue
        residual = h
        while residual % 7 == 0:
            residual //= 7
        if residual != 1:
            continue
        d = -abs_d
        forms = list(reduced_forms(d))
        assert len(forms) == h
        tested.append(d)
        if all(class_power(f,7,d) == forms[0] for f in forms):
            hits.append(abs_d)
    assert hits == list(ABS_DISCRIMINANTS)
    print("Absolute discriminant ceiling:",LIMIT)
    print("Order discriminants checked:",sum(h != 0 for h in counts))
    print("Candidate orders with class number a nontrivial power of seven:",len(tested))
    print("Orders of exact exponent seven:",len(hits))
    print("Exact match to Table A.7 throughout this full finite range.")


if __name__ == "__main__":
    run()
