#!/usr/bin/env python3
"""Generate or independently recompute a deterministic exact evidence document."""
import argparse
from functools import lru_cache
import json
import sys
from exact import (VerificationError, require, recurrence, radical_coefficients,
                   interleave, algebraic_residuals, inverse_identity_evidence)
from permutations import counterexample_evidence, exhaustive_evidence
from safeio import read_regular, write_fresh

SCHEMA = 'report149.corrected-baxter.exact-evidence.v1'
HALF_LENGTH = 60
REFERENCE_PREFIX = [1,1,1,1,2,2,3,5,8,12,16,32,44,84,105,231,292,636,
                    768,1792,2168,5080,6014,14594,17252]


def canonical_bytes(data):
    return (json.dumps(data, sort_keys=True, indent=2, ensure_ascii=False,
                       allow_nan=False) + '\n').encode('utf-8')


def build_evidence():
    even, odd = recurrence(HALF_LENGTH)
    r_even, r_odd = radical_coefficients(HALF_LENGTH)
    require((even, odd) == (r_even, r_odd), "recurrence and radical disagree")
    corrected = interleave(even, odd)
    require(corrected[:len(REFERENCE_PREFIX)] == REFERENCE_PREFIX,
            "reference prefix changed")
    old_even, old_odd = recurrence(HALF_LENGTH, corrected=False)
    old = interleave(old_even, old_odd)
    discrepancies = [n for n, (a, b) in enumerate(zip(corrected, old)) if a != b]
    require(bool(discrepancies) and discrepancies[0] == 20, "first discrepancy changed")
    require(corrected[20] == 2168 and old[20] == 2166, "n20 values changed")
    evidence = {
        "schema": SCHEMA,
        "arithmetic": "Python standard library integers and fractions.Fraction only",
        "conventions": {"a_2m": "e_m", "a_2m_plus_1": "o_m",
                        "alternation": "ascent first: p1<p2>p3<...",
                        "empty_permutation": 1,
                        "corrected_factor": "C_j=binomial(2j,j)/(j+1)",
                        "old_recurrence_factor": "o_j from the old recurrence itself"},
        "exact_coefficients": {
            "inclusive_half_length_bound": HALF_LENGTH,
            "recurrence_even": even, "recurrence_odd": odd,
            "radical_even": r_even, "radical_odd": r_odd,
            "old_recurrence_even": old_even, "old_recurrence_odd": old_odd,
            "first_discrepancy": {"n": 20, "corrected": 2168, "old": 2166},
            "algebraic_residuals_through_degree_60": algebraic_residuals(even, odd)},
        "counterexamples": counterexample_evidence(),
        "finite_exhaustive_checks": exhaustive_evidence(corrected),
        "formal_inverse": inverse_identity_evidence(),
        "sources": [
            {"title": "Min and Park, 2006", "doi": "https://doi.org/10.4134/JKMS.2006.43.3.553",
             "used_for": "Unrestricted structural grammar, Theorem 4.1 and Corollaries 4.5, 4.7"},
            {"title": "Min, 2021", "doi": "https://doi.org/10.14403/jcms.2021.34.3.253",
             "used_for": "Literal strict value-adjacency definition on p.253 and old recurrence comparison"}],
        "limitations": [
            "The all-n corrected counting theorem relies on the written combinatorial proof and its cited structural lemmas.",
            "Direct, lemma-independent exhaustive permutation counting stops at n=12.",
            "The larger structural enumeration assumes the unrestricted structural lemmas, and is labeled accordingly.",
            "Formal inverse identities do not certify finite error constants, onsets, or universally exact ceiling rounding.",
            "This evidence does not certify novelty, literature completeness, or the current contents of an external OEIS entry."]
    }
    return evidence


@lru_cache(maxsize=1)
def _expected_bytes():
    # Cached immutable bytes, not a caller-mutable dictionary.
    return canonical_bytes(build_evidence())


def validate_evidence(data):
    """Recompute semantic evidence; no embedded digest or claimed flag is trusted.

    Exact key sets, types, bounds, claims and coefficient values must all match.
    Comparing canonical bytes distinguishes JSON booleans from integers too.
    """
    require(type(data) is dict, "evidence root must be an object")
    try:
        encoded = canonical_bytes(data)
    except (ValueError, TypeError) as exc:
        raise VerificationError("invalid JSON evidence data") from exc
    require(encoded == _expected_bytes(), "evidence differs from exact recomputation")
    return True


def decode_evidence(payload):
    def unique_pairs(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate JSON key: " + key)
            result[key] = value
        return result
    def reject_constant(value):
        raise VerificationError("non-finite JSON constant: " + value)
    try:
        return json.loads(payload.decode('utf-8'), object_pairs_hook=unique_pairs,
                          parse_constant=reject_constant)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError("invalid UTF-8 JSON") from exc


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument('--output', metavar='FRESH_JSON_FILE',
                         help='create a new evidence file; never overwrite or follow symlinks')
    actions.add_argument('--check', metavar='EXISTING_JSON_FILE',
                         help='recompute all evidence and reject any semantic mismatch')
    args = parser.parse_args(argv)
    try:
        if args.output:
            write_fresh(args.output, _expected_bytes())
            print('Exact evidence generated and verified')
        else:
            validate_evidence(decode_evidence(read_regular(args.check)))
            print('Exact evidence verified by recomputation')
    except (VerificationError, OSError, ValueError, RuntimeError) as exc:
        print('Verification failed: ' + str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
