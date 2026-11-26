"""Check the progression-avoidance argument uniformly in the odd-prime block.

The four symbols 0,1,2,H stand for individual exponents 0,1,2 or an
unspecified Rankin exponent at least 3. The only mathematical input to
the reduction is that Rankin exponents contain no nonconstant 3-term AP.
A progression with at least one added term uses at most three exceptional
odd primes (one per added term). Every other odd valuation equals 1 at
the new term and is good everywhere, hence equals 1 in all three terms.
Deleting those constant coordinates leaves the same test for old-point
survival. False positives are allowed in the local AP test; a negative
outcome therefore certifies impossibility for every choice of exponents.
"""
from itertools import product

HIGH = 3
GOOD = (0,1,HIGH)


def possible_ap(a, b, c):
    if 2 not in (a,b,c):
        # All three concrete values belong to the AP-free Rankin exponent set.
        return a==b==c
    if HIGH not in (a,b,c):
        return a+c==2*b
    # Two equal concrete (small) values force all three to be equal.
    for x in (0,1,2):
        if (a,b,c).count(x)>=2:
            return False
    # Conservatively allow every remaining pattern involving a large value.
    return True


def check(k):
    old=[]
    for vector in product(GOOD,repeat=k+1):
        exceptions=[x for x in vector[1:] if x!=1]
        if exceptions and exceptions != [HIGH]:
            old.append(vector)
    new=[(2,)+tuple(2 if i==j else 1 for i in range(k)) for j in range(k)]
    checked=0
    for mask in product((0,1), repeat=3):
        if not any(mask):
            continue
        choices=[new if flag else old for flag in mask]
        for a,b,c in product(*choices):
            checked+=1
            if all(possible_ap(x,y,z) for x,y,z in zip(a,b,c)):
                # New vectors at a specified prime have exactly the displayed
                # concrete exponents everywhere; equal vectors are equal terms.
                assert all(mask) and a==b==c
    return checked


if __name__=='__main__':
    for k in (1,2,3):
        print(k,"exceptional odd primes:",check(k),"abstract triples verified")
