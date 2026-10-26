"""Finite independent arithmetic checks for the oriented reciprocal theorem.

These checks supplement, and do not replace, its unbounded proof.
Standard library only; no assertions so -O preserves every check.
"""
from fractions import Fraction
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pell(a, k):
    x, y = 1, 0
    for _ in range(abs(k)):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, -y if k < 0 else y


def block(a, n, requests):
    t = 2*a*n-n*n-1
    h = s = error_sq = 0
    for m, k in requests:
        x, y = pell(a, k)
        z = a*y
        h += y*(m-x)
        s += (m-x+z)**2-y*y
        error_sq += (m-x+z-n*y)**2
    e = s-2*n*h
    require(error_sq == e-t*sum(pell(a,k)[1]**2 for _, k in requests),
            "completed-square identity")
    return t, e, error_sq


def rational(a, blocks):
    data = [block(a, n, req) for n, req in blocks]
    q = sum((Fraction(n*e,t) for (n,_),(t,e,_) in zip(blocks,data)), Fraction())
    r = sum((Fraction(n*s,t) for (n,_),(t,_,s) in zip(blocks,data)), Fraction())
    require((q-r).denominator == 1, "rational square identity")
    product = 1
    for t,_,_ in data:
        product *= t
    numerator = sum(n*e*(product//t) for (n,_),(t,e,_) in zip(blocks,data))
    require(Fraction(numerator, product) == q, "cleared polynomial identity")
    return q


def main():
    w = 258
    a0 = w**w+1
    tested = invalid = identities = 0
    choices = [
        [0, 1, -1, 2, -3],
        [3, -2, 0, -1, 1],
        [0, 0, 0, 0, 0],
        [2, 2, -2, -2, 0],
    ]
    for a in (a0, -a0):
        for bases in choices:
            blocks = []
            for j, n in enumerate(bases):
                ks = [-2, -1, 0, 1] if abs(n) == 1 else [0, 1, 2]
                if n == 0:
                    req = [(7,-2),(-3,1),(0,2)]
                else:
                    req = [((1 if n == 1 or k % 2 == 0 else -1)
                            if k < 0 else n**k, k) for k in ks]
                blocks.append((n,req))
            require(sum(len(r) for _,r in blocks)<=17, "request limit")
            require(all(n*n<w and m*m<w and k*k<w
                        for n,req in blocks for m,k in req), "frame bounds")
            value = rational(a,blocks)
            require(value.denominator == 1, "true power completion")
            tested += 1
            identities += sum(len(r) for _,r in blocks)
            for j,(n,req) in enumerate(blocks):
                if n == 0:
                    continue
                for kidx in range(len(req)):
                    changed = [(nn,list(rr)) for nn,rr in blocks]
                    m,k = changed[j][1][kidx]
                    changed[j][1][kidx] = (m+1,k)
                    require(rational(a,changed).denominator != 1,
                            "incorrect output escaped oriented pool")
                    invalid += 1
    # Negative indices at nonunit bases cannot have integer exact outputs.
    for a in (a0,-a0):
        for n in (-3,-2,2,3):
            for k in (-2,-1):
                for m in range(-2,3):
                    require(rational(a,[(n,[(m,k)])]).denominator != 1,
                            "negative nonunit index escaped")
                    invalid += 1
    result = {"status":"PASS", "valid_mixed_sign_and_zero_profiles":tested,
              "canonical_request_instances":identities,
              "invalid_outputs_or_indices_rejected":invalid,
              "W":w,"A_description":"both signs of 258^258+1",
              "proof_scope":"Finite arithmetic fixtures, not unbounded theorem verification."}
    print(json.dumps(result, indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
