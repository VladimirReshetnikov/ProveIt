#!/usr/bin/env python3
"""Independent orbit, finite-difference and precision checks for this review.

The oracle for scalar coefficients enumerates row choices using integer
polynomial multiplication, never a finite-difference or polarization formula.
The orbit checker constructs involution classes independently of the box rule.
"""
from __future__ import annotations

import itertools
import json
import argparse
from math import prod
from pathlib import Path
import random

from streamed_coefficients import (
    _antipodal_boxes, coefficient_antipodal_gray, coefficient_gray,
)
from baseline_packet_extraction import RingSpec


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def scalar_integer_oracle(forms, beta):
    zero = (0,) * len(beta)
    polynomial = {zero: 1}
    for row in forms:
        following = {}
        for exponent, value in polynomial.items():
            following[exponent] = following.get(exponent, 0) + value * row[0]
            for j in range(len(beta)):
                if exponent[j] < beta[j]:
                    key = list(exponent)
                    key[j] += 1
                    key = tuple(key)
                    following[key] = following.get(key, 0) + value * row[j + 1]
        polynomial = following
    return polynomial.get(tuple(beta), 0)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,
        default=Path(__file__).resolve().parents[1]/"results/local_checks/independent_review.json")
    args=parser.parse_args()
    orbit_cases = orbit_pairs = scalar_cases = invariant_cases = 0
    # Includes all-even cases with several zero-width prefix axes.
    for dimension in range(1, 5):
        for exponents in itertools.product(range(5), repeat=dimension):
            if not 0 < sum(exponents) <= 12:
                continue
            points = set(itertools.product(*(range(b + 1) for b in exponents)))
            fixed = {g for g in points if all(2*x == b for x,b in zip(g,exponents))}
            classes = {
                frozenset((g, tuple(b - x for x,b in zip(g,exponents))))
                for g in points - fixed
            }
            representatives = []
            for start, limits in _antipodal_boxes(exponents):
                representatives.extend(
                    tuple(s+x for s,x in zip(start,offset))
                    for offset in itertools.product(*(range(v+1) for v in limits))
                )
            require(len(representatives) == len(set(representatives)), "overlapping boxes")
            require(set(representatives) <= points - fixed, "invalid representative")
            require(all(len(c & set(representatives)) == 1 for c in classes),
                    "an orbit has zero or two representatives")
            require(len(representatives) == prod(b+1 for b in exponents)//2,
                    "wrong half-grid count")
            orbit_cases += 1
            orbit_pairs += len(classes)

    rng = random.Random(927104)
    for R in range(7):
        for dimension in range(4):
            for _ in range(10):
                beta = tuple(rng.randrange(R+2) for _ in range(dimension))
                forms = [[rng.randrange(-7,8) for _ in range(dimension+1)] for _ in range(R)]
                p = rng.randrange(1,9)
                encoded = [[(x,) for x in row] for row in forms]
                oracle = scalar_integer_oracle(forms,beta) % (1 << p)
                gray = coefficient_gray(encoded,beta,p)
                paired = coefficient_antipodal_gray(encoded,beta,p)
                require(gray.coefficient == paired.coefficient == (oracle,), "integer oracle mismatch")
                # Coefficients are canonically fixed at input p, regardless of
                # the temporary precision used by the extraction method.
                lifted = [[(x + rng.randrange(-9,10)*(1<<p),) for x in row] for row in forms]
                again = coefficient_antipodal_gray(lifted,beta,p)
                require(again == paired, "creation-precision representatives changed")
                invariant_cases += 1
                if sum(beta) <= R and R:
                    b = (R-sum(beta),*beta)
                    nu = sum(x-x.bit_count() for x in b)
                    odd_mass = sum(x for x in b if x % 2)
                    require(paired.working_precision == p+nu+odd_mass-1,
                            "wrong anisotropic precision")
                    require(paired.working_precision >= p, "precision below target")
                scalar_cases += 1

    # Explicit all-even, smallest-precision examples with nonzero answers.
    # Their factorial denominator loses a factor two by pairing.
    fixtures = [([[(0,),(1,)],[(0,),(1,)]],(2,),1,(1,)),
                ([[ (1,), (1,) ]]*4,(2,),2,(2,)),
                ([[ (1,), (1,) ]]*6,(2,),4,(15,))]
    for forms,beta,p,answer in fixtures:
        paired=coefficient_antipodal_gray(forms,beta,p,RingSpec())
        require(paired.coefficient == answer, "all-even precision fixture failed")
        require(paired.working_precision == coefficient_gray(forms,beta,p).working_precision-1,
                "all-even case did not save one precision bit")

    result = {"status":"passed", "orbit_profiles":orbit_cases,
              "antipodal_orbits":orbit_pairs,"integer_oracle_cases":scalar_cases,
              "canonical_representative_cases":invariant_cases,
              "all_even_low_precision_fixtures":len(fixtures),"seed":927104}
    output=args.output
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
