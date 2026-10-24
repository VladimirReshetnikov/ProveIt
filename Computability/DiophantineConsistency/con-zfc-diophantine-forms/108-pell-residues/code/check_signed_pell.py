#!/usr/bin/env python3
"""Finite regression checks for the signed auxiliary Pell theorem.

The unbounded theorem is proved in the article. These exact integer checks
exercise all four sign choices, the half-modulus boundary, and two necessary
hypotheses. They are not a proof by search. Standard library only.
"""
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pell(a, n):
    x, y = 1, 0
    for _ in range(n):
        x, y = a*x+(a*a-1)*y, x+a*y
    return x, y


def run():
    accepted = checked = negative_auxiliary = 0
    absolute_value_counterexample = None
    for a in range(2, 8):
        for i in (1, 2):
            x, y = pell(a, i)
            m = 2*i*y
            u, v = pell(a, m)
            require(v % (y*y) == 0 and m % y == 0, "Pell divisibility")
            b = a+u*((1-a)*pow(u, -1, 4*y) % (4*y))
            require(b >= a and b % (4*y) == 1, "CRT base")
            for factor in (2, 4):
                modulus = factor*y
                # Two simultaneous modular recurrences avoid huge coordinates.
                xu, yu = 1 % u, 0
                xr, yr = 1 % modulus, 0
                for j in range(4*m+3):
                    for sign_s in (-1, 1):
                        for sign_r in (-1, 1):
                            for k in range(1, y+1):
                                checked += 1
                                satisfies = ((sign_s*xu-x) % u == 0 and
                                             (sign_r*yr-k) % modulus == 0)
                                if satisfies:
                                    require(k == i, "signed criterion failed")
                                    accepted += 1
                                    if sign_s < 0 or (sign_r < 0 and j > 0):
                                        negative_auxiliary += 1
                                    if sign_s < 0 and (xu-x) % u:
                                        absolute_value_counterexample = {
                                            "a":a,"main_index":i,"auxiliary_index":m,
                                            "signed_pair_index":j,"modulus_factor":factor,
                                            "sign_s":sign_s,"sign_r":sign_r,
                                            "explanation":"Replacing S by abs(S) breaks S=X mod U."
                                        }
                    xu, yu = ((b*xu+(b*b-1)*yu) % u,
                              (xu+b*yu) % u)
                    xr, yr = ((b*xr+(b*b-1)*yr) % modulus,
                              (xr+b*yr) % modulus)
    require(negative_auxiliary > 0, "No signed examples exercised")
    require(absolute_value_counterexample is not None, "Missing absolute-value control")
    # Without the target bound, k and k+4Y have identical congruences.
    a, i = 2, 2
    x, y = pell(a, i)
    m = 2*i*y
    u, v = pell(a, m)
    b = a+u*((1-a)*pow(u, -1, 4*y) % (4*y))
    s, r = pell(b, i)
    wrong_k = i+4*y
    require((s-x) % u == 0 and (r-wrong_k) % (4*y) == 0,
            "Missing target-bound counterexample")
    require(pell(a, wrong_k) != (x,y), "Target-bound control is trivial")
    # Without the R congruence, an unrelated k in [1,Y] would be accepted.
    require(1 <= 1 <= y and i != 1 and (r-1) % (4*y) != 0,
            "Missing ordinate-congruence counterexample")
    return {
        "status":"pass", "assignments_checked":checked,
        "signed_certificates_accepted":accepted,
        "accepted_with_negative_auxiliary":negative_auxiliary,
        "absolute_value_counterexample":absolute_value_counterexample,
        "negative_controls":["target upper bound is necessary",
                             "ordinate congruence is necessary",
                             "absolute values alone do not restore auxiliary congruences"],
        "scope":"Finite regression checks; the article supplies the unbounded proof."
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
