#!/usr/bin/env python3
"""Fail-closed finite exact verifier for report105; standard library only.

Commands (run from any directory):
    python3 code/verify_exact.py
    python3 -O code/verify_exact.py
    python3 code/run_checks.py
    python3 code/verify_exact.py --certificate OTHER.json --terms OTHER.txt

Only integers and fractions are used in mathematical checks. Success means
all specified FINITE checks passed. It is not an analytic proof of any limit,
uniform estimate, transcendental inequality, or asymptotic error bound.
Malformed, incomplete, duplicate-key, extra, and altered certificate entries
fail before the expensive recurrence whenever preflight can detect them.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

CURRENT_PHASE = "preflight"

from exact_models import (BRUTE_N, FIXED_D, MAX_N, OEIS_INITIAL, POLYNOMIAL_N,
    POWER_B, SHIFT_D, CheckFailure, brute_force, canonical_bytes,
    expected_certificate, require)


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def reject_noninteger_number(value):
    raise CheckFailure("non-integer JSON number is forbidden: " + value)


def parse_certificate(path):
    raw = path.read_bytes()
    require(len(raw) <= 8_000_000, "certificate exceeds size limit")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=no_duplicate_keys,
        parse_float=reject_noninteger_number, parse_constant=reject_noninteger_number)


def same_structure(actual, expected, path="certificate"):
    require(type(actual) is type(expected), path + ": wrong JSON type")
    if type(expected) is dict:
        require(actual.keys() == expected.keys(), path + ": missing or extra keys")
        for key in expected:
            same_structure(actual[key], expected[key], path + "." + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), path + ": missing or extra cases")
        for index, (left, right) in enumerate(zip(actual, expected)):
            same_structure(left, right, path + "[" + str(index) + "]")
    else:
        require(actual == expected, path + ": value mismatch")


def parse_terms(path):
    raw = path.read_bytes()
    require(len(raw) <= 2_000_000, "term file exceeds size limit")
    require(raw.endswith(b"\n"), "term file must end in a newline")
    lines = raw.splitlines()
    require(len(lines) == MAX_N + 1, "term file must contain exactly 501 lines")
    terms = []
    for n, line in enumerate(lines):
        require(re.fullmatch(rb"(?:0|[1-9][0-9]*) [1-9][0-9]*", line) is not None,
                "noncanonical term line at n=" + str(n))
        index, value = map(int, line.split(b" "))
        require(index == n, "missing, duplicate, or misordered term index")
        terms.append(value)
    require(tuple(terms[:len(OEIS_INITIAL)]) == OEIS_INITIAL, "initial OEIS terms mismatch")
    return raw, terms


def check_polynomial_identities(polynomials):
    # Independent coefficient-level check of the original uncancelled kernel
    # relation, including its exceptional n=0 term.
    checks = 0
    for n, gn in enumerate(polynomials):
        lhs = [0] * (len(gn) + 1)
        for t, coefficient in enumerate(gn):
            lhs[t] += coefficient
            lhs[t + 1] -= coefficient
        if n == 0:
            require(lhs == [0, 1, -1], "kernel constant coefficient")
        else:
            rhs = [0] * len(lhs)
            # u*g_(n-j)(u+z*u*(1-u)): choose j powers of z.
            from math import comb
            for j in range(1, n + 1):
                for t, coefficient in enumerate(polynomials[n-j]):
                    if t < j:
                        continue
                    for k in range(j + 1):
                        rhs[t + 1 + k] += coefficient * comb(t, j) * comb(j, k) * (-1) ** k
            require(lhs == rhs, "uncancelled formal kernel coefficient n=" + str(n))
            require(sum(gn) == sum(t * c for t, c in enumerate(polynomials[n - 1])),
                    "formal derivative evaluation at one n=" + str(n))
        checks += 1
    return checks


def check_fixed_d(cases):
    comparisons = children = 0
    for case in cases:
        d = case["d"]
        layers = []
        for n, encoded in enumerate(case["state_layers"]):
            stored = {(K, L): count for K, L, count in encoded}
            direct = brute_force(d, n)
            require(stored == direct, "brute-force state mismatch d=" + str(d) + ", n=" + str(n))
            count = 1 if n == 0 else sum(direct.values())
            require(count == case["counts"][n], "brute-force count mismatch")
            layers.append(direct)
            comparisons += 1
        for n in range(1, BRUTE_N):
            weighted = sum((K + 2) * count for (K, L), count in layers[n].items())
            require(weighted == case["counts"][n + 1], "fixed-d children identity")
            children += 1
    return {"brute_force_full_state_comparisons": comparisons,
            "fixed_d_children_identities": children}


def matrix_vector(M, v, vector, d):
    return [sum((v if j > l-d else 1) * vector[j] for j in range(M)) for l in range(M)]


def check_frozen(cases):
    eigen = shifted = powers = 0
    for case in cases:
        M, r, v = case["M"], F(case["r"]), F(case["v"])
        lam = F(case["lambda"])
        f = list(map(F, case["f"]))
        require(v == r ** (-M) and all(x > 0 for x in f) and lam > 0,
                "frozen positivity or rational parametrization")
        action = matrix_vector(M, v, f, 1)
        for l in range(M):
            require(action[l] == lam * f[l], "exact Perron eigenvector identity")
            eigen += 1
        condition = max(v, 1 / v)
        require(max(f) / min(f) <= condition, "eigenvector condition bound")
        for d in SHIFT_D:
            C = abs(d - 1) * abs(v - 1) * condition
            action = matrix_vector(M, v, f, d)
            for l in range(M):
                require(action[l] <= (lam + C) * f[l], "fixed-band supersolution")
                changed = sum((j >= l) != (j > l-d) for j in range(M))
                require(changed <= abs(d - 1), "fixed-band altered-entry count")
                shifted += 1
            vector = [F(1)] * M
            for b in range(max(POWER_B) + 1):
                if b in POWER_B:
                    for l in range(M):
                        require(vector[l] <= condition * (lam + C) ** b,
                                "positive matrix power bound")
                        powers += 1
                if b < max(POWER_B):
                    vector = matrix_vector(M, v, vector, d)
    return {"frozen_cases": len(cases), "eigenvector_rows": eigen,
            "fixed_band_rows": shifted, "matrix_power_rows": powers}


def check_poisson(cases):
    poisson_rows = h_formula_values = doob_entries = stationary = tracking = drift = 0
    wrap_loss_cases = mean_cases = 0
    for case in cases:
        M, r = case["M"], F(case["r"])
        B, D = r / (1-r), 1-r ** M
        v, lam = r ** (-M), (r ** (-M)-1)/(1-r)
        p = [(1-r) * r ** k / D for k in range(M)]
        require(sum(p) == 1 and all(t > 0 for t in p), "geometric transition probabilities")
        P = [[p[(j-l) % M] for j in range(M)] for l in range(M)]
        for l in range(M):
            require(sum(P[l]) == 1, "Markov row sum")
            for j in range(M):
                doob = (v if j >= l else 1) * r ** j / (lam * r ** l)
                require(P[l][j] == doob, "circulant Doob transform")
                doob_entries += 1
        for j in range(M):
            require(sum(P[l][j] for l in range(M)) == 1, "uniform stationarity")
        b_direct = [sum(P[l][j] * int(j >= l) * F(j, M) for j in range(M))
                    for l in range(M)]
        b, c, h = list(map(F, case["b_over_q"])), F(case["c_over_q"]), list(map(F, case["h_over_q"]))
        require(b == b_direct, "b/q finite-sum formula")
        require(c == sum(b_direct) / M, "c/q stationary mean formula")
        require(0 <= c <= F(M-1, 2*M) <= F(1, 2), "c/q stationary upper bound")
        EW = sum(p[k] * F(k, M) for k in range(M))
        EW2 = sum(p[k] * F(k, M) ** 2 for k in range(M))
        mean_formula = B/M - r**M/D
        require(EW == mean_formula == F(case["mean_W"]), "exact geometric mean formula")
        require(0 <= EW <= F(M-1, 2*M) <= F(1, 2), "geometric mean interval")
        mean_cases += 1
        for forward in range(M):
            # Average over uniformly distributed starting letters, conditional
            # on this fixed forward circular increment.
            loss = F(0)
            for start in range(M):
                output = (start + forward) % M
                if output < start:
                    loss += F(output, M*M)
            require(loss == F(forward*(forward-1), 2*M*M)
                    == F(case["wrap_losses"][forward]), "exact stationary wrap loss")
            wrap_loss_cases += 1
        require(c == (1-EW2)/2 - (1-EW)/(2*M), "c/q circular-moment identity")
        stationary += 1
        # Independent stable form after division by q; includes seam l=M.
        A_over_q = M * (1/r-1) / (2*D)
        J_over_q = r ** M / D - B / M
        for l in range(M + 1):
            x = F(l, M)
            stable_h = A_over_q * x * (1-x) + J_over_q * x
            require(h[l] == stable_h, "h/q quadratic versus stable formula")
            h_formula_values += 1
        require(h[M] - h[0] == J_over_q <= 0, "normalized corrector seam")
        for l in range(M):
            ph = sum(P[l][j] * h[j] for j in range(M))
            require(ph - h[l] == c - b[l], "(P-I)h/q = c/q - b/q")
            poisson_rows += 1
            mean_increment = F(0)
            for j in range(M):
                a = int(j >= l)
                W = F((j-l) % M, M)
                old_x, new_x = F(l, M), F(j, M+a)
                increment = a - new_x + old_x
                require(increment == 1-W + F(a, M)*new_x,
                        "exact tracked-state increment")
                mean_increment += P[l][j] * increment
                tracking += 1
            require(mean_increment >= F(1, 2), "finite tracked-state drift lower bound")
            drift += 1
    return {"poisson_cases": len(cases), "doob_entries": doob_entries,
        "h_over_q_formula_values": h_formula_values, "poisson_rows": poisson_rows,
        "stationary_mean_and_moment_cases": stationary,
        "tracked_state_identities": tracking, "finite_drift_rows": drift, "geometric_mean_formulas": mean_cases,
        "stationary_wrap_loss_cases": wrap_loss_cases}


def check_positive_recurrence(terms, polynomials):
    require(terms[0] == terms[1] == 1, "base counts")
    layer = [[1]]
    require(polynomials[0] == [0, 1], "g_0")
    require(polynomials[1] == [0, 0, 1], "g_1")
    polynomial_comparisons = 2
    children = 0
    nonnegative_entries = 1
    support_entries = 1
    for n in range(2, MAX_N + 1):
        weighted_children = sum((k + 2) * sum(row) for k, row in enumerate(layer))
        new_layer = []
        for k in range(n):
            old = layer[k] if k < len(layer) else []
            previous = layer[k - 1] if k else []
            tail = sum(old)
            prefix = 0
            row = []
            for j in range(k + 1):
                if j < len(old):
                    tail -= old[j]
                if j < len(previous):
                    prefix += previous[j]
                value = tail + prefix
                require(value >= 0, "positive recurrence produced a negative entry")
                row.append(value)
            if any(row):
                require(2*n <= (k+1)*(k+2), "weak-ascent deterministic support bound")
                support_entries += sum(value > 0 for value in row)
            nonnegative_entries += len(row)
            new_layer.append(row)
        layer = new_layer
        row_counts = [sum(row) for row in layer]
        total = sum(row_counts)
        require(total == terms[n], "regenerated term mismatch at n=" + str(n))
        require(total == weighted_children, "exact children identity at n=" + str(n-1))
        children += 1
        if n <= POLYNOMIAL_N:
            require([0, 0] + row_counts == polynomials[n],
                    "full derivative polynomial versus positive recurrence at n=" + str(n))
            polynomial_comparisons += 1
    return {"regenerated_terms": MAX_N + 1, "maximum_n": MAX_N,
        "children_identities": children,
        "full_polynomial_comparisons": polynomial_comparisons,
        "nonnegative_state_entries": nonnegative_entries,
        "nonzero_states_with_deterministic_support": support_entries}


def run(certificate_path, terms_path):
    global CURRENT_PHASE
    CURRENT_PHASE = "preflight"
    certificate = parse_certificate(certificate_path)
    raw, terms = parse_terms(terms_path)
    expected = expected_certificate(raw)
    same_structure(certificate, expected)
    CURRENT_PHASE = "finite_algebra"
    # Everything below is recomputed independently of claims stored in JSON.
    summary = {"status": "passed", "arithmetic": "integer_and_rational_only",
        "scope": "Finite checks only; not analytic proofs.",
        "python_optimization": sys.flags.optimize,
        "strict_certificate_inventory": "complete",
        "terms_sha256": sha256(raw).hexdigest(),
        "certificate_semantic_sha256": sha256(canonical_bytes(certificate)).hexdigest(),
        "oeis_initial_terms_compared": len(OEIS_INITIAL)}
    summary["formal_kernel_coefficients"] = check_polynomial_identities(certificate["polynomials"])
    summary.update(check_fixed_d(certificate["fixed_d_cases"]))
    summary.update(check_frozen(certificate["frozen_cases"]))
    summary.update(check_poisson(certificate["poisson_cases"]))
    CURRENT_PHASE = "positive_recurrence"
    summary.update(check_positive_recurrence(terms, certificate["polynomials"]))
    return summary


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=root/"data"/"exact_certificate.json")
    parser.add_argument("--terms", type=Path, default=root/"data"/"weak_ascent_terms.txt")
    args = parser.parse_args()
    try:
        result = run(args.certificate, args.terms)
    except Exception as error:
        # An unexpected implementation error must fail closed as well.
        print(json.dumps({"status": "failed", "error_type": type(error).__name__,
                          "error": str(error), "phase": CURRENT_PHASE}), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
