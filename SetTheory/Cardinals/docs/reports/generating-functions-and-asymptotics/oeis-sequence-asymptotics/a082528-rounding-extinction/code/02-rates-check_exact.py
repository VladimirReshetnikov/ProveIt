#!/usr/bin/env python3
"""Report188 mandatory finite exact checks, valid under Python -I -S -O.

Only integers and Fraction participate in the mathematical checks. The checker
is an executable finite test suite, not a machine-checked proof of asymptotics.
All checks and input guards are explicit exceptions, never assert statements.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("report188_exact_rounding", HERE / "exact_rounding.py")
if SPEC is None or SPEC.loader is None:
    raise ImportError("Cannot load exact_rounding.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
FIXTURE_PATH = HERE.parent / "data" / "oeis_fixtures.json"
POWERS = tuple(Fraction(a, b) for a, b in ((1, 3), (1, 2), (2, 3), (1, 1), (3, 2), (2, 1), (5, 2), (3, 1), (4, 1)))
EXPECTED_RECORDS = {
    "A002491": (1, 53, "threshold", 1),
    "A073047": (1, 79, "stopping_index", 1),
    "A082527": (0, 105, "stopping_index", 2),
    "A082528": (0, 105, "stopping_index", 3),
}


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def reference_terminal(n, k, p):
    """Independent exact forward method: binary search each quotient.

    Does not call the production integer-root, forward, or reverse routines.
    """
    M.integer(n, "n")
    M.integer(k, "k", 1)
    p = M.rational(p, "p", True)
    a, b, q = p.numerator, p.denominator, n
    for j in range(2, k + 1):
        numerator = q ** b * (j - 1) ** a
        lo, hi = 0, q + 1
        while hi - lo > 1:
            middle = (lo + hi) // 2
            if middle ** b * j ** a <= numerator:
                lo = middle
            else:
                hi = middle
        q = lo
    return q


def reference_threshold(k, p, h=1):
    """Independent least-boundary search, using only reference forward runs."""
    M.integer(k, "k", 1)
    M.integer(h, "h", 1)
    p = M.rational(p, "p", True)
    lo, hi = 0, h
    while reference_terminal(hi, k, p) < h:
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        middle = (lo + hi) // 2
        if reference_terminal(middle, k, p) >= h:
            hi = middle
        else:
            lo = middle
    return hi


def invariant_by_cells(p, u):
    """Independent multiplicative integration of 1/(v+r) on each cell."""
    p, u = M.rational(p, "p", True), M.rational(u, "u")
    result, left, r = Fraction(1), Fraction(0), 1
    while left < u:
        right = min(u, Fraction(r) / p)
        result *= (r + right) / (r + left)
        left, r = right, r + 1
    return result


def validate_profile(values, k, p, h=1):
    """Check every defining reverse inequality, including strict minimality."""
    M.integer(k, "k", 1)
    M.integer(h, "h", 1)
    p = M.rational(p, "p", True)
    if not isinstance(values, (list, tuple)) or len(values) != k + 1:
        raise ValueError("profile shape")
    for q in values:
        M.integer(q, "profile entry")
    require(values[0] == 0 and values[-1] == h, "profile endpoints")
    a, b = p.numerator, p.denominator
    for j in range(1, k):
        r, target = values[j], (j + 1) ** a * values[j + 1] ** b
        require(r >= 1, "positive reverse quotient")
        require((r - 1) ** b * j ** a < target <= r ** b * j ** a, "reverse defining inequality")
    return True


def reject_duplicate_keys(pairs):
    """Reject ambiguous JSON objects instead of silently keeping the last key."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate fixture JSON key: " + key)
        result[key] = value
    return result


def reject_nonfinite_constant(value):
    raise ValueError("nonfinite fixture JSON constant: " + value)


def parse_fixture_json(raw):
    """Strict fixture parser: no duplicate keys or nonstandard numeric constants."""
    return json.loads(raw, object_pairs_hook=reject_duplicate_keys,
                      parse_constant=reject_nonfinite_constant)


def validate_fixtures(data):
    if not isinstance(data, dict) or set(data) != {"schema_version", "attribution", "license", "license_url", "source_scope", "records"}:
        raise ValueError("fixture top-level schema")
    if type(data["schema_version"]) is not int or data["schema_version"] != 1:
        raise ValueError("fixture schema version")
    for key in ("attribution", "license", "license_url", "source_scope"):
        if not isinstance(data[key], str) or not data[key]:
            raise ValueError("fixture provenance field " + key)
    records = data["records"]
    if not isinstance(records, list) or len(records) != 4:
        raise ValueError("four records required")
    seen = set()
    keys = {"id", "offset", "kind", "power", "term_count", "terms", "record_revision", "record_date", "record_author", "source_url", "data_url", "record_sha256"}
    for record in records:
        if not isinstance(record, dict) or set(record) != keys:
            raise ValueError("fixture record schema")
        identifier = record["id"]
        if identifier not in EXPECTED_RECORDS or identifier in seen:
            raise ValueError("unknown or repeated sequence")
        seen.add(identifier)
        offset, count, kind, power = EXPECTED_RECORDS[identifier]
        for key in ("offset", "power", "term_count", "record_revision"):
            M.integer(record[key], key)
        if (record["offset"], record["term_count"], record["kind"], record["power"]) != (offset, count, kind, power):
            raise ValueError("fixture sequence convention or count")
        if not isinstance(record["terms"], list) or len(record["terms"]) != count:
            raise ValueError("fixture term count")
        for term in record["terms"]:
            M.integer(term, "OEIS term", 1)
        for key in ("record_date", "record_author", "source_url", "data_url", "record_sha256"):
            if not isinstance(record[key], str) or not record[key]:
                raise ValueError("fixture provenance field " + key)
        if record["source_url"] != "https://oeis.org/" + identifier:
            raise ValueError("fixture source URL")
        digest = record["record_sha256"]
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            raise ValueError("source record digest")
    return records


def check_fixture_terms(data):
    count = 0
    for record in validate_fixtures(data):
        p = Fraction(record["power"])
        operation = M.threshold if record["kind"] == "threshold" else M.stopping_index
        for index, expected in enumerate(record["terms"], record["offset"]):
            require(operation(index, p) == expected, record["id"] + " term " + str(index))
            count += 1
    return count


def expect_failure(label, exception, function, *args):
    try:
        function(*args)
    except exception:
        return 1
    except Exception as error:
        raise ArithmeticError(label + " raised wrong exception: " + type(error).__name__) from error
    raise ArithmeticError(label + " did not reject bad input")


def input_guard_checks():
    checks = 0
    cases = [
        (TypeError, M.rational_power, (True, 1)),
        (TypeError, M.rational_power, (1, False)),
        (TypeError, M.rational_power, (1.0, 2)),
        (ValueError, M.rational_power, (0, 1)),
        (ValueError, M.rational_power, (-1, 2)),
        (ValueError, M.rational_power, (1, 0)),
        (ValueError, M.rational_power, (1, -2)),
    ]
    for function in (M.floor_root_ratio, M.ceil_root_ratio):
        for arguments, error in (((True, 1, 2), TypeError), ((1, True, 2), TypeError), ((1, 1, True), TypeError), ((-1, 1, 2), ValueError), ((1, 0, 2), ValueError), ((1, 1, 0), ValueError), ((1.0, 1, 2), TypeError)):
            cases.append((error, function, arguments))
    for function in (M.reverse_profile, M.threshold, reference_threshold):
        for arguments, error in (((True, 1, 1), TypeError), ((0, 1, 1), ValueError), ((1, True, 1), TypeError), ((1, 0, 1), ValueError), ((1, -1, 1), ValueError), ((1, 0.5, 1), TypeError), ((1, 1, True), TypeError), ((1, 1, 0), ValueError), ((1, 1, -1), ValueError)):
            cases.append((error, function, arguments))
    for function in (M.forward_profile, M.terminal_quotient, reference_terminal):
        for arguments, error in (((True, 1, 1), TypeError), ((-1, 1, 1), ValueError), ((1, False, 1), TypeError), ((1, 0, 1), ValueError), ((1, 1, True), TypeError), ((1, 1, 0), ValueError), ((1, 1, 0.5), TypeError)):
            cases.append((error, function, arguments))
    for arguments, error in (((True, 1), TypeError), ((-1, 1), ValueError), ((1, True), TypeError), ((1, 0), ValueError), ((1, -1), ValueError), ((1, 0.5), TypeError)):
        cases.append((error, M.stopping_index, arguments))
    for function in (M.gamma_product,):
        for arguments, error in (((True, 1), TypeError), ((0, 1), ValueError), ((1, True), TypeError), ((1, -1), ValueError), ((1, 1.0), TypeError)):
            cases.append((error, function, arguments))
    for function in (M.drift_function, M.invariant_exp, invariant_by_cells):
        for arguments, error in (((True, 1), TypeError), ((0, 1), ValueError), ((1, True), TypeError), ((1, -1), ValueError), ((1, 0.5), TypeError)):
            cases.append((error, function, arguments))
    for function in (M.profile_u, M.profile_mass_power):
        for arguments, error in (((True, 1), TypeError), ((0, 1), ValueError), ((1, True), TypeError), ((1, 0), ValueError), ((1, -1), ValueError), ((1, 2), ValueError), ((1, 0.5), TypeError)):
            cases.append((error, function, arguments))
    for exception, function, arguments in cases:
        checks += expect_failure(function.__name__, exception, function, *arguments)
    require(M.rational_power(6, 4) == Fraction(3, 2), "rational parameter reduction")
    require(M.reverse_profile(20, M.rational_power(6, 4)) == M.reverse_profile(20, Fraction(3, 2)), "reduced parameter equivalence")
    return checks


def corruption_checks(data):
    checks = 0
    serialized = json.dumps(data, sort_keys=True)
    duplicate = '{"schema_version": 999,' + serialized[1:]
    checks += expect_failure("duplicate JSON key", ValueError, parse_fixture_json, duplicate)
    for token in ("NaN", "Infinity", "-Infinity"):
        bad_json = serialized.replace('"schema_version": 1', '"schema_version": ' + token, 1)
        checks += expect_failure("nonfinite JSON constant " + token, ValueError, parse_fixture_json, bad_json)
    checks += expect_failure("explicit certificate failure", ArithmeticError, require, False, "intentional corruption")
    bad = copy.deepcopy(data)
    bad["records"][0]["terms"][0] += 1
    checks += expect_failure("corrupted integer fixture", ArithmeticError, check_fixture_terms, bad)
    bad = copy.deepcopy(data)
    bad["records"][1]["terms"][0] = True
    checks += expect_failure("bool fixture term", TypeError, validate_fixtures, bad)
    bad = copy.deepcopy(data)
    bad["records"][2]["terms"].pop()
    checks += expect_failure("truncated fixture", ValueError, validate_fixtures, bad)
    bad = copy.deepcopy(data)
    bad["records"][3]["offset"] = 1
    checks += expect_failure("wrong offset", ValueError, validate_fixtures, bad)
    bad = list(M.reverse_profile(12, Fraction(2, 3), 4))
    bad[5] += 1
    checks += expect_failure("corrupted reverse quotient", ArithmeticError, validate_profile, bad, 12, Fraction(2, 3), 4)
    bad = list(M.reverse_profile(12, Fraction(2, 3), 4))
    bad[-1] = 5
    checks += expect_failure("corrupted terminal mass", ArithmeticError, validate_profile, bad, 12, Fraction(2, 3), 4)
    bad = list(M.reverse_profile(12, Fraction(2, 3), 4))
    bad[0] = True
    checks += expect_failure("bool profile entry", TypeError, validate_profile, bad, 12, Fraction(2, 3), 4)
    return checks


def run():
    fixture_bytes = FIXTURE_PATH.read_bytes()
    data = parse_fixture_json(fixture_bytes)
    counts = {"oeis_terms": check_fixture_terms(data), "input_rejections": input_guard_checks(), "corruption_rejections": corruption_checks(data)}
    root_count = 0
    for numerator in range(81):
        for denominator in range(1, 14):
            for degree in range(1, 8):
                lower = M.floor_root_ratio(numerator, denominator, degree)
                upper = M.ceil_root_ratio(numerator, denominator, degree)
                require(denominator * lower ** degree <= numerator < denominator * (lower + 1) ** degree, "floor root boundary")
                require(denominator * upper ** degree >= numerator and (upper == 0 or denominator * (upper - 1) ** degree < numerator), "ceil root boundary")
                root_count += 1
    counts["root_ratio_pairs"] = root_count
    counts.update({"minimal_profiles": 0, "adjacent_stopping_boundaries": 0, "forward_reverse_entries": 0, "drift_sandwiches": 0, "integer_power_tails": 0, "terminal_profiles": 0, "terminal_boundaries": 0, "independent_thresholds": 0, "independent_forward_values": 0, "product_breakpoints": 0, "neighboring_cell_agreements": 0, "rational_profile_points": 0})
    for p in POWERS:
        previous_threshold = 0
        for k in range(1, 61):
            q = M.reverse_profile(k, p)
            validate_profile(q, k, p)
            boundary = q[1]
            require(boundary > previous_threshold, "strict threshold increase")
            previous_threshold = boundary
            require(M.stopping_index(boundary - 1, p) == k, "lower stopping boundary")
            require(M.stopping_index(boundary, p) == k + 1, "upper stopping boundary")
            counts["adjacent_stopping_boundaries"] += 2
            forward = M.forward_profile(boundary, k, p)
            for j in range(1, k + 1):
                require(forward[j] == q[j], "forward/reverse realization")
                counts["forward_reverse_entries"] += 1
            for j in range(1, k):
                u, v = Fraction(q[j + 1], j + 1), Fraction(q[j], j)
                require(M.drift_function(p, u) <= j * (v - u) <= M.drift_function(p, v), "drift sandwich")
                counts["drift_sandwiches"] += 1
                if p.denominator == 1:
                    a = p.numerator
                    residues = [i ** a * q[i] - (i + 1) ** a * q[i + 1] for i in range(1, j)]
                    require(all(0 <= residue < i ** a for i, residue in enumerate(residues, 1)), "rounding residue range")
                    require(boundary - j ** a * q[j] == sum(residues), "telescoping identity")
                    require(0 <= sum(residues) <= sum(i ** a for i in range(1, j)), "tail bound")
                    counts["integer_power_tails"] += 1
            counts["minimal_profiles"] += 1
        for k in range(1, 31):
            for h in sorted({1, 2, max(1, k // 2), k, 2 * k}):
                q = M.reverse_profile(k, p, h)
                validate_profile(q, k, p, h)
                boundary = q[1]
                require(M.terminal_quotient(boundary, k, p) == h, "terminal upper boundary")
                require(M.terminal_quotient(boundary - 1, k, p) < h, "terminal lower boundary")
                require(M.forward_profile(boundary, k, p) == q, "whole terminal trajectory realized")
                require(reference_threshold(k, p, h) == boundary, "independent threshold reference")
                counts["terminal_profiles"] += 1
                counts["terminal_boundaries"] += 2
                counts["independent_thresholds"] += 1
        for n in range(81):
            for k in range(1, 13):
                require(M.terminal_quotient(n, k, p) == reference_terminal(n, k, p), "independent forward grid")
                counts["independent_forward_values"] += 1
        previous = Fraction(1)
        for r in range(1, 31):
            current = M.gamma_product(p, r)
            u = Fraction(r) / p
            require(M.invariant_exp(p, u) == invariant_by_cells(p, u) == 1 / current, "product breakpoint")
            left_value = previous * (r + Fraction(r - 1) / p) / (r + u)
            right_value = current * (r + 1 + Fraction(r) / p) / (r + 1 + u)
            require(left_value == right_value == current, "neighbor cell continuity")
            require(M.profile_u(p, current) == u, "profile breakpoint inverse")
            counts["product_breakpoints"] += 1
            counts["neighboring_cell_agreements"] += 1
            for numerator in range(5):
                t = (numerator * current + (4 - numerator) * previous) / 4
                v = M.profile_u(p, t)
                require(Fraction(r - 1) / p <= v <= Fraction(r) / p, "profile cell range")
                require(M.invariant_exp(p, v) * t == 1, "profile exact inversion")
                require(invariant_by_cells(p, v) * t == 1, "independent profile inversion")
                require(M.profile_mass_power(p, t) == t ** (p.numerator + p.denominator) * v ** p.denominator, "rational mass power")
                counts["rational_profile_points"] += 1
            previous = current
        require(M.invariant_exp(p, 0) == 1 and M.drift_function(p, 0) == 1, "zero endpoints")
        require(M.profile_u(p, 1) == 0 and M.profile_mass_power(p, 1) == 0, "profile t=1")
        require(M.stopping_index(0, p) == 1, "first-zero convention")
    samples = []
    for p in (Fraction(1), Fraction(2), Fraction(3), Fraction(4), Fraction(1, 2), Fraction(3, 2)):
        for k in (100, 1000, 10000):
            samples.append({"p": str(p), "k": k, "threshold": M.threshold(k, p)})
    return {
        "schema_version": 1,
        "status": "passed",
        "arithmetic": "integer and Fraction only",
        "scope": "Finite exact identities and threshold checks; no floating Gamma intervals or asymptotic proof certificate",
        "fixture_sha256": hashlib.sha256(fixture_bytes).hexdigest(),
        "powers": [str(p) for p in POWERS],
        "domains": {
            "root_numerator": [0, 80], "root_denominator": [1, 13], "root_degree": [1, 7],
            "minimal_profile_k": [1, 60], "terminal_profile_k": [1, 30],
            "terminal_h": "distinct values in {1,2,max(1,k//2),k,2*k}",
            "independent_forward_n": [0, 80], "independent_forward_k": [1, 12],
            "profile_cells": [1, 30], "profile_cell_interpolation_numerators_over_4": [0, 1, 2, 3, 4],
        },
        "counts": counts,
        "threshold_samples": samples,
    }


def write_output(path, text):
    """Create a fresh nonsymlink output outside the immutable source package."""
    target = path.absolute()
    for component in (target, *target.parents):
        if component.is_symlink():
            raise ValueError("output path must not contain symlinks")
    resolved = target.resolve()
    source_root = HERE.parent.resolve()
    if resolved == source_root or source_root in resolved.parents:
        raise ValueError("output must be outside the source package")
    if not target.parent.is_dir():
        raise ValueError("output parent directory must already exist")
    with target.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write deterministic JSON here as well as stdout")
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        write_output(args.output, result)
    print(result, end="")


if __name__ == "__main__":
    main()
