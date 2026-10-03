#!/usr/bin/env python3
"""Standalone exact-Poly regressions; standard library only.

Run directly for the corrected module, or pass --baseline-module PATH to also
reproduce the delivered constructor defects and check unchanged exact algebra.
"""
from __future__ import annotations

import argparse
import copy
from dataclasses import FrozenInstanceError
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import random
import sys
import tempfile

import sparse_mass as repaired


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def rejects(call):
    try:
        call()
    except ValueError:
        return
    raise AssertionError("malformed polynomial was accepted")


def load_module(path):
    spec = importlib.util.spec_from_file_location("sparse_mass_delivered_baseline", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run(baseline=None):
    P = repaired.Poly
    class IntSubclass(int):
        pass

    bad = {
        "mutable_outer": [((0,), 1)],
        "missing_outer": None,
        "mapping_outer": {},
        "mutable_pair": ([(0,), 1],),
        "empty_pair": ((),),
        "short_pair": (((0,),),),
        "long_pair": (((0,), 1, 2),),
        "mutable_monomial": (([0], 1),),
        "bool_index": (((True,), 1),),
        "float_index": (((0.0,), 1),),
        "fraction_index": (((Fraction(0),), 1),),
        "string_index": ((("x",), 1),),
        "integer_subclass_index": (((IntSubclass(0),), 1),),
        "bool_coefficient": (((0,), True),),
        "float_coefficient": (((0,), 1.0),),
        "nan_coefficient": (((0,), float("nan")),),
        "infinite_coefficient": (((0,), float("inf")),),
        "fraction_coefficient": (((0,), Fraction(1)),),
        "string_coefficient": (((0,), "1"),),
        "integer_subclass_coefficient": (((0,), IntSubclass(1)),),
        "zero_coefficient": (((0,), 0),),
        "unsorted_monomial": (((1, 0), 1),),
        "duplicate_monomials": (((0,), 1), ((0,), 2)),
        "unsorted_terms": (((1,), 1), ((0,), 1)),
    }
    for terms in bad.values():
        rejects(lambda terms=terms: P(terms))

    huge = 2**60
    witness = huge + 1
    float_terms = (((), float(huge)), ((0,), -1.0))
    rejects(lambda: P(float_terms))
    exact = P((((), huge), ((0,), -1)))
    b = repaired.Builder()
    b.new("x", witness)
    b.constrain("exact residual minus one", exact)
    need(exact.evaluate([witness]) == -1, "integer residual changed")
    need(not b.validate_witness() and b.score() == 1, "false integer zero")
    need(type(b.score()) is int, "integer score was coerced")

    # Repetition of a variable denotes a power and remains valid; negative
    # indices denote free parameters. Neither is a malformed monomial.
    repeated = P((((-2, -1, 0, 0), -3),))
    need(repeated.evaluate([5], [7, 11]) == -5775, "powers or parameters changed")
    for p in (P(()), P((((), 1),)), repeated):
        try:
            p.terms = ()
        except FrozenInstanceError:
            pass
        else:
            raise AssertionError("frozen polynomial is mutable")
    terms = [[(1, 0), 2], [(0, 1), -1], [(), 0]]
    canonical = P.make(terms)
    need(canonical.terms == (((0, 1), 1),), "make did not canonicalize")
    terms[0][1] = 999
    need(canonical.terms == (((0, 1), 1),), "make retains mutable aliases")
    for invalid in (True, 1.0, Fraction(1), "1"):
        rejects(lambda invalid=invalid: P.make([((), invalid)]))
        rejects(lambda invalid=invalid: P.constant(invalid))
        rejects(lambda invalid=invalid: P.variable(invalid))

    # Independently evaluate the raw input terms, rather than using Poly's
    # evaluation to predict the result of its own arithmetic.
    rng = random.Random(20261003)
    algebra_cases = 300
    algebra_comparisons = 0
    def raw_value(raw, values, parameters):
        total = 0
        for monomial, coefficient in raw:
            product = coefficient
            for i in monomial:
                product *= values[i] if i >= 0 else parameters[-i-1]
            total += product
        return total
    for _ in range(algebra_cases):
        raw = [[([rng.randrange(-2, 3) for _ in range(rng.randrange(4))],
                 rng.randrange(-10**18, 10**18)) for _ in range(10)] for _ in range(2)]
        values = [rng.randrange(10**18) for _ in range(3)]
        parameters = [rng.randrange(10**18) for _ in range(2)]
        a, c = (P.make(t) for t in raw)
        av, cv = (raw_value(t, values, parameters) for t in raw)
        expressions = (a, c, a+c, a-c, a*c, -a, 7-a, 7+a, 7*a)
        expected = (av, cv, av+cv, av-cv, av*cv, -av, 7-av, 7+av, 7*av)
        for polynomial, value in zip(expressions, expected):
            actual = polynomial.evaluate(values, parameters)
            need(type(actual) is int and actual == value, "exact algebra mismatch")
            need(P(polynomial.terms) == polynomial, "algebra is not canonical")
            algebra_comparisons += 1
        if baseline:
            old_a, old_c = (baseline.Poly.make(t) for t in raw)
            old = (old_a, old_c, old_a+old_c, old_a-old_c, old_a*old_c,
                   -old_a, 7-old_a, 7+old_a, 7*old_a)
            need([p.terms for p in old] == [p.terms for p in expressions],
                 "valid polynomial coefficients changed from baseline")

    # JSON already enforces exact integer coefficients. Exercise the actual
    # bound verifier, including a float equal to the original integer value.
    fixture = Path(__file__).parent / "fixtures/binary_three_way_collision.json"
    payload = json.loads(fixture.read_text())
    bound_checks = 0
    for module in ([repaired, baseline] if baseline else [repaired]):
        need(module.verify_bound_export(fixture)["valid"], "valid fixture rejected")
        for scalar in (1.0, True):
            rejects(lambda scalar=scalar, module=module:
                    module.Poly.from_json([[[], scalar]], 0, 0))
        damaged = copy.deepcopy(payload)
        damaged["residuals"][0][0][1] = float(damaged["residuals"][0][0][1])
        with tempfile.TemporaryDirectory(prefix="poly-domain-") as directory:
            path = Path(directory) / "float-coefficient.json"
            path.write_text(json.dumps(damaged))
            rejects(lambda module=module: module.verify_bound_export(path))
        bound_checks += 1

    result = {
        "status": "PASS",
        "malformed_direct_constructor_cases_rejected": len(bad),
        "float_false_zero_constructor_rejected": True,
        "exact_residual": -1,
        "exact_score": 1,
        "exact_arithmetic_random_cases": algebra_cases,
        "exact_arithmetic_expression_comparisons": algebra_comparisons,
        "canonicalization_and_mutation_isolation": True,
        "repeated_variable_powers_and_signed_parameter_indices_preserved": True,
        "bound_verifier_float_rejection_modules_checked": bound_checks,
        "seed": 20261003,
    }
    if baseline:
        old = baseline.Poly(float_terms)
        old_builder = baseline.Builder()
        old_builder.new("x", witness)
        old_builder.constrain("inexact residual minus one", old)
        need(old.evaluate([witness]) == 0.0 and old_builder.validate_witness(),
             "baseline false-zero reproduction failed")
        mutable = [[(0,), 1]]
        old_mutable = baseline.Poly(mutable)
        before = old_mutable.evaluate([3])
        mutable[0][1] = 2
        need(before == 3 and old_mutable.evaluate([3]) == 6,
             "baseline mutable-alias reproduction failed")
        for malformed in ("unsorted_monomial", "duplicate_monomials", "unsorted_terms"):
            baseline.Poly(bad[malformed])
        result["baseline"] = {
            "float_residual": old.evaluate([witness]),
            "witness": witness,
            "false_zero_accepted": old_builder.validate_witness(),
            "score": old_builder.score(),
            "mutable_evaluation_before": before,
            "mutable_evaluation_after": old_mutable.evaluate([3]),
            "noncanonical_examples_accepted": 3,
            "exact_expression_coefficient_comparisons": algebra_comparisons,
        }
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-module", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(load_module(args.baseline_module) if args.baseline_module else None)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
