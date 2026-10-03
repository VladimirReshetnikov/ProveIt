"""Reproduce all finite exact-arithmetic checks reported in the article."""
from __future__ import annotations
import json
from collections import Counter
from itertools import product
from pathlib import Path
from random import Random
from time import perf_counter
from quantum_diophantine import *

ROOT = Path(__file__).resolve().parents[1]
COUNTS: Counter = Counter()

def check(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)
    COUNTS[label] += 1


def inspect_instrument(ins: Instrument, depth: int) -> None:
    d, r = ins.d, ins.r
    k, dimension = len(ins.kraus), ins.dimension
    alpha, beta = F(4, 5)/ins.c, F(3, 5)
    n, hh = ins.integer_numerators()
    total = zero(dimension, dimension)
    for a in ins.kraus:
        total = add(total, gram(a))
    check(total == eye(dimension), "instrument_normalization")
    for length in range(1, depth+1):
        for word in product(range(k), repeat=length):
            p = word_product(ins.kraus, word)
            active = [i-1 for i in word if i]
            mp = word_product(ins.original, active)
            top = tuple(tuple(row[:d]) for row in p[:d])
            z = word.count(0)
            check(top == scale(alpha**len(active)*beta**z, mp), "top_projection_identity")
            if active:
                erased = tuple(i for i in word if i)
                ep = word_product(ins.kraus, erased)
                check(iszero(p) == iszero(ep), "idle_erasure_zero_equivalence")
                if iszero(p):
                    check(iszero(mp), "no_spurious_mortality")
                if iszero(mp):
                    for label in range(1, k):
                        check(iszero(mul(ins.kraus[label], p)), "one_step_flush")
            else:
                check(not iszero(p), "idle_only_nonzero")
            probability = sum((x*x for row in p for x in row), F(0))/dimension
            hp = word_product(hh, word)
            numerator = sum((x*x for row in hp for x in row), F(0))
            check(probability == numerator / (dimension*n**(2*length)), "probability_integer_formula")
            check(probability == 0 or probability >= F(1, dimension*n**(2*length)), "arithmetic_gap")
            check(0 <= probability <= 1, "probability_range")


def main() -> None:
    start = perf_counter()
    for n in range(301):
        check(sum(x*x for x in four_squares(n)) == n, "four_squares")
    rng = Random(20260930)
    random_count = 0
    for d in [1, 2]:
        for k in [1, 2, 3]:
            for _ in range(2):
                ms = [matrix([[rng.randint(-1, 1) for _ in range(d)] for _ in range(d)])
                      for _ in range(k)]
                ins = compile_instrument(ms)
                inspect_instrument(ins, 3)
                random_count += 1
    sample = signed_example()
    inspect_instrument(sample, 4)
    elementary = compile_instrument(sample.original, c=3)
    check(elementary.dimension == 5, "elementary_dimension_five")
    inspect_instrument(elementary, 2)
    # Directly exercise the existence-search backend on small inputs. This is
    # NOT a performance claim for general six-generator mortality instances.
    qcases = [matrix([[7]]), matrix([[2,1],[1,2]]), scale(5, eye(3))]
    for q in qcases:
        b = gram_search(q, max_height=2)
        check(gram(b) == q and len(b) == len(q)+3, "meyer_search_small_case")
    b = gram_search(scale(5, eye(3)), max_height=2)
    searched = compile_instrument(sample.original, c=3, factor=b)
    inspect_instrument(searched, 2)
    check(searched.dimension == 4, "searched_dimension_four")
    try:
        gram_search(matrix([[7]]), s=3, max_height=2)
    except TimeoutError:
        COUNTS["height_cap_correctly_signalled"] += 1
    else:
        raise AssertionError("7 incorrectly represented by three rational squares")
    check(sample.probability((2,1)) == F(64,50625), "signed_example_positive_prefix")
    check(sample.probability((2,1,1)) == 0, "signed_example_zero_flush")
    check(iszero(word_product(sample.original, (1,0))), "signed_cancellation_original")
    ab = [matrix([[abs(x) for x in row] for row in a]) for a in sample.original]
    check(not iszero(word_product(ab, (1,0))), "absolute_value_surrogate_fails")
    # Endpoint sharpness: source shortest length 1; target shortest length 2.
    plusone = compile_instrument([matrix([[0]])], c=1, factor=matrix([[1]]))
    check(not iszero(plusone.kraus[1]) and iszero(mul(plusone.kraus[1], plusone.kraus[1])),
          "length_plus_one_sharp")
    # Equality endpoint: a zero source generator gets a zero Gram block.
    equal = compile_instrument([matrix([[0]]), matrix([[1]])], c=2,
                               factor=matrix([[0],[0],[0],[1],[1],[1]]))
    check(iszero(equal.kraus[1]), "length_equality_sharp")
    # Uniform symbolic certificate, including signed free input parameters.
    hsmall = [matrix([[1,1],[0,0]]), matrix([[1,0],[-1,0]])]
    cert = build_certificate(2, 2, 2)
    expanded = cert.expanded()
    check(expanded.degree == 4, "expanded_quartic_degree")
    for word in product(range(2), repeat=2):
        assignment = canonical_assignment(hsmall, word)
        value = cert.value(assignment)
        check((value == 0) == iszero(word_product(hsmall, word)), "certificate_equivalence")
        check(expanded.evaluate(assignment) == value, "expanded_matches_residual_sum")
        if value == 0:
            for name in cert.witnesses:
                mutant = dict(assignment)
                mutant[name] += 1
                check(cert.value(mutant) != 0, "single_coordinate_mutation_rejected")
    # Full four-dimensional, seven-outcome sample certificate.
    n, numerators = sample.integer_numerators()
    full = build_certificate(4, 7, 3)
    assignment = canonical_assignment(numerators, (2,1,1))
    check(full.value(assignment) == 0, "four_dimensional_certificate")
    for name in full.witnesses:
        mutant = dict(assignment)
        mutant[name] += 1
        check(full.value(mutant) != 0, "full_certificate_mutation_rejected")
    (ROOT/"examples").mkdir(exist_ok=True)
    data = {"dimension": 4, "outcomes": 7, "common_denominator": n,
            "chronological_zero_word": [2,1,1],
            "positive_prefix_probability": "64/50625",
            "H": [[[int(x) for x in row] for row in a] for a in numerators],
            "gram_factor": [[str(x) for x in row] for row in sample.factor]}
    (ROOT/"examples"/"four_dimensional_instrument.json").write_text(json.dumps(data, indent=2)+"\n")
    poly_data = {"D": 2, "K": 2, "n": 2, "degree": expanded.degree,
                 "witness_count": len(cert.witnesses), "residual_count": len(cert.residuals),
                 "witnesses": cert.witnesses, "inputs": cert.inputs,
                 "polynomial": expanded.as_json()}
    (ROOT/"examples"/"quartic_D2_K2_n2.json").write_text(json.dumps(poly_data, indent=2)+"\n")
    (ROOT/"examples"/"zero_word_witness.json").write_text(json.dumps(assignment, indent=2)+"\n")
    report = {"status": "PASS", "seed": 20260930, "arithmetic": "exact integers and Fraction",
              "random_instruments": random_count, "checks": dict(sorted(COUNTS.items())),
              "total_checks": sum(COUNTS.values()),
              "small_expanded_quartic_monomials": len(expanded.terms),
              "small_certificate_witnesses": len(cert.witnesses),
              "small_certificate_residuals": len(cert.residuals),
              "full_certificate_witnesses": len(full.witnesses),
              "full_certificate_residuals": len(full.residuals),
              "runtime_seconds": round(perf_counter()-start, 3),
              "not_verified": ["unbounded undecidability by finite testing", "Lean formalization",
                               "efficient general d+3 Gram factorization", "novelty priority"]}
    (ROOT/"verification").mkdir(exist_ok=True)
    (ROOT/"verification"/"check_results.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
