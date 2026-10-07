#!/usr/bin/env python3
"""Regenerate Report216 exact receipts and optional numerical diagnostics."""
import argparse
import copy
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import platform
import re
import sys
import extremes as core
import independent as check

HERE = Path(__file__).resolve().parent
CASES = [(kind, k, b) for k, b in ((2, 0), (2, 1), (3, 0), (2, 3))
         for kind in ("E", "T")]
ORDERS = (0, 1, 2, 3, 6)
SCHEMA = "Report216-v1"


def dumps(data):
    return json.dumps(data, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def source_hashes():
    return {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
            for name in ("extremes.py", "independent.py", "reproduce.py")}


def metadata():
    return {"schema": SCHEMA, "python": platform.python_version(),
            "source_sha256": source_hashes()}


def require_keys(data, expected):
    if type(data) is not dict or set(data) != set(expected):
        raise ValueError("receipt object has unexpected keys")


def parse_laurent(record):
    if type(record) is not dict:
        raise ValueError("polynomial must be an exponent-to-rational object")
    result = {}
    for e, c in record.items():
        if type(e) is not str or not re.fullmatch(r"0|-?[1-9][0-9]*", e):
            raise ValueError("noncanonical exponent")
        if type(c) is not str or not re.fullmatch(r"-?[1-9][0-9]*(/[1-9][0-9]*)?", c):
            raise ValueError("noncanonical nonzero rational")
        coefficient = F(c)
        if str(coefficient) != c:
            raise ValueError("rational must be reduced")
        result[int(e)] = coefficient
    return core.Laurent(result)


def validate_coefficient_case(row):
    require_keys(row, ("kind", "k", "b", "order", "c", "u"))
    s = core.parameters(row["kind"], row["k"], row["b"], row["order"])
    R = row["order"]
    if type(row["c"]) is not list or type(row["u"]) is not list:
        raise ValueError("coefficient lists required")
    if len(row["c"]) != R + 1 or len(row["u"]) != R + 1:
        raise ValueError("coefficient list length mismatch")
    c, u = [[parse_laurent(v) for v in row[key]] for key in ("c", "u")]
    if c != core.forward_coefficients(row["kind"], row["k"], row["b"], R):
        raise ValueError("forward coefficients disagree with exact regeneration")
    if any(core.inverse_residual(c, s + 2, u, R)):
        raise ValueError("inverse coefficients fail formal identity")
    return c, u


def validate_selected_counts(row):
    require_keys(row, ("kind", "k", "b", "counts"))
    core.parameters(row["kind"], row["k"], row["b"], 0)
    if type(row["counts"]) is not dict or not row["counts"]:
        raise ValueError("nonempty selected-count dictionary required")
    ns = []
    for n, value in row["counts"].items():
        if type(n) is not str or not re.fullmatch(r"0|[1-9][0-9]*", n):
            raise ValueError("noncanonical count index")
        if type(value) is not str or not re.fullmatch(r"0|[1-9][0-9]*", value):
            raise ValueError("counts must be canonical nonnegative integer strings")
        ns.append(int(n))
    fresh = core.exact_counts(row["kind"], row["k"], row["b"], max(ns))
    if any(str(fresh[n]) != row["counts"][str(n)] for n in ns):
        raise ValueError("selected counts disagree with exact regeneration")


def expect_rejected(action, label):
    try:
        action()
    except (ValueError, RuntimeError, TypeError):
        return label
    raise RuntimeError("negative control was accepted: " + label)


def negative_controls(sample_coefficients, sample_counts):
    tests = []
    for args in (("X", 2, 0, 2), ("E", 1, 0, 2), ("E", 2, -1, 2),
                 ("E", 2, 0, -1), ("E", 2.0, 0, 2), ("E", True, 0, 2),
                 ("E", 2, False, 2), ("E", 2, 0, 1.5)):
        tests.append(expect_rejected(lambda a=args: core.forward_coefficients(*a),
                                     "domain:" + repr(args)))
    for value in (float("nan"), float("inf"), 0.5, True, {1: 0.5}, {True: 1}):
        tests.append(expect_rejected(lambda v=value: core.Laurent(v), "inexact Laurent:" + repr(value)))
    tests.append(expect_rejected(lambda: core.revert_coefficients([core.ZERO], 4), "unnormalized c0"))
    tests.append(expect_rejected(lambda: core.inverse_residual([core.ONE], 4, [core.ONE], 0), "nonzero delta0"))
    tests.append(expect_rejected(lambda: check.require(False, "intentional"), "explicit guard"))
    bad = copy.deepcopy(sample_coefficients); bad["c"][0] = {"0": "2"}
    tests.append(expect_rejected(lambda: validate_coefficient_case(bad), "poisoned c0 receipt"))
    bad_u = copy.deepcopy(sample_coefficients); bad_u["u"][1] = {}
    tests.append(expect_rejected(lambda: validate_coefficient_case(bad_u), "poisoned u1 receipt"))
    bad_rational = copy.deepcopy(sample_coefficients); bad_rational["c"][1] = {"0": "2/2"}
    tests.append(expect_rejected(lambda: validate_coefficient_case(bad_rational), "unreduced rational receipt"))
    bad_count = copy.deepcopy(sample_counts); bad_count["counts"]["0"] = "1"
    tests.append(expect_rejected(lambda: validate_selected_counts(bad_count), "poisoned exact count receipt"))
    bad_negative = copy.deepcopy(sample_counts); bad_negative["counts"]["0"] = "-1"
    tests.append(expect_rejected(lambda: validate_selected_counts(bad_negative), "negative count receipt"))
    bad_boolean = copy.deepcopy(sample_counts); bad_boolean["counts"]["0"] = False
    tests.append(expect_rejected(lambda: validate_selected_counts(bad_boolean), "boolean count receipt"))
    return tests


def exact_outputs():
    N = 160; ks = range(2, 9); bs = range(7)
    direct = check.direct_counts(N, ks, bs)
    check.require(tuple(check.partition_coin_change(N)) == core.partition_numbers(N), "partition recurrence mismatch")
    points = 0
    for (kind, k, b), expected in direct.items():
        actual = core.exact_counts(kind, k, b, N)
        check.require(actual == expected, f"exact count mismatch {(kind, k, b)}")
        points += len(actual)
        if kind == "E" and b < 6:
            check.require(actual == [x - y for x, y in zip(direct["T", k, b], direct["T", k, b + 1])], "tail difference mismatch")
    for ell in range(21):
        check.require(check.q_recurrence(ell) == core.q_polynomial(ell), "Q recurrence mismatch")
    algebra_cases = 0
    for k in range(2, 11):
        for b in (0, 1, 2, 7):
            for kind in ("E", "T"):
                s = k if kind == "E" else k - 1; R = 6
                check.require(check.radial_moments(kind, k, b, s + R) == core.radial_coefficients(kind, k, b, s + R), "radial moment mismatch")
                c = core.forward_coefficients(kind, k, b, R)
                check.require(c == check.forward_moments(kind, k, b, R), "forward transfer mismatch")
                check.require(c[0] == core.ONE, "c0 normalization")
                base = F(-k * (k + 5), 4) - b - (12 if k == 2 else 0) if kind == "E" else F(-(k * (k + 5) - 2), 4) - b - (6 if k == 2 else 0)
                invA = F(-(k + 1) * (k + 2), 4) if kind == "E" else F(-k * (k + 1), 4)
                check.require(c[1] == core.Laurent({0: base, -1: invA}), "c1 closed form")
                u = core.revert_coefficients(c, s + 2)
                check.require(not any(check.inverse_residual_via_derivative(c, s + 2, u)), "independent inverse residual")
                check.require(u[1] == -2 * core.A * c[1], "u1 formula")
                check.require(u[2] == -2 * core.A * (s + 2) * c[1] - 4 * core.A ** 2 * c[2] + 2 * core.A ** 2 * c[1] ** 2, "u2 formula")
                d = s + 2
                u3 = (-F(8, 3) * core.A ** 3 * c[1] ** 3
                      + 8 * core.A ** 3 * c[1] * c[2] - 8 * core.A ** 3 * c[3]
                      + 2 * core.A ** 2 * d * c[1] ** 2 - 4 * core.A ** 2 * c[1] ** 2
                      - 4 * core.A ** 2 * d * c[2] - 2 * core.A * d ** 2 * c[1])
                check.require(u[3] == u3, "u3 formula")
                algebra_cases += 1
    depth_checks = 0
    for k in range(2, 25):
        for R in range(30):
            J = (R + 3 + k - 2) // (k - 1)
            check.require(F((k - 1) * J) - F(3, 2) >= R + 1, "insufficient Cauchy depth")
            depth_checks += 1
    coefficients = []
    counts = []
    for kind, k, b in CASES:
        c = core.forward_coefficients(kind, k, b, 6)
        u = core.inverse_coefficients(kind, k, b, 6)
        row = {"kind": kind, "k": k, "b": b, "order": 6,
               "c": [v.record() for v in c], "u": [v.record() for v in u]}
        validate_coefficient_case(row); coefficients.append(row)
        row = {"kind": kind, "k": k, "b": b,
               "counts": {str(n): str(direct[kind, k, b][n]) for n in (0, 1, 2, 3, 10, 20, 40, 80, 160)}}
        validate_selected_counts(row); counts.append(row)
    negative = negative_controls(coefficients[0], counts[0])
    receipt = metadata() | {"status": "PASS", "exact_count_cases": len(direct),
        "exact_coefficient_comparisons": points, "n_range": [0, 160], "k_range": [2, 8], "b_range": [0, 6],
        "moment_transfer_inverse_cases": algebra_cases, "relative_orders": [0, 6],
        "Q_recurrence_through_ell": 20, "cauchy_depth_checks": depth_checks,
        "negative_controls_passed": negative,
        "guard_note": "Explicit exceptions; no assertions. Normal and -O receipts are identical.",
        "independence_note": "Distinct count and algebra algorithms adapted from the research audit; not clean-room authorship."}
    return {"results/exact_checks.json": dumps(receipt),
            "results/coefficients.json": dumps(metadata() | {"variable": "A", "encoding": "exponent -> reduced rational string; zero polynomial is {}", "cases": coefficients}),
            "results/selected_counts.json": dumps(metadata() | {"cases": counts})}


def evaluate(poly, A, mp):
    return sum((mp.mpf(c.numerator) / c.denominator * A ** e for e, c in poly.terms), mp.mpf(0))


def diagnostics_outputs():
    try:
        import mpmath as mp
    except ImportError as error:
        raise RuntimeError("Optional diagnostics require mpmath; see README.md") from error
    mp.mp.dps = 80
    A = mp.pi ** 2 / 6
    rows = []
    for kind, k, b in CASES:
        print(f"diagnostics: {kind} k={k} b={b}", file=sys.stderr, flush=True)
        exact = core.exact_counts(kind, k, b, 10001)
        c_exact = core.forward_coefficients(kind, k, b, 6)
        c = [evaluate(v, A, mp) for v in c_exact]
        u = [evaluate(v, A, mp) for v in core.revert_coefficients(c_exact, (k if kind == "E" else k - 1) + 2)]
        s = k if kind == "E" else k - 1; d = s + 2
        D = factorial(k) * 2 ** s * A ** (s + 1) / mp.sqrt(3)
        for n in (1000, 10000):
            y = exact[n]; N = mp.mpf(n) - mp.mpf(1) / 24
            t = mp.sqrt(A / N); B = mp.exp(2 * mp.sqrt(A * N)) / (4 * mp.sqrt(3) * N)
            w0 = -d * mp.lambertw(-(D / y) ** (mp.mpf(1) / d) / d, -1)
            if not mp.isfinite(w0) or abs(mp.im(w0)) > mp.mpf("1e-70"):
                raise RuntimeError("Lambert branch did not produce a finite real core")
            w0 = mp.re(w0)
            check.require(exact[n - 1] < y <= exact[n + 1], "nearby threshold comparison failed")
            threshold = next(i for i, value in enumerate(exact[:n + 1]) if value >= y)
            check.require(threshold == n, "global finite threshold scan failed")
            approximations = []
            for order in ORDERS:
                forward = factorial(k) * B * t ** s * sum(c[j] * t ** j for j in range(order + 1))
                delta = sum((u[j] / w0 ** j for j in range(1, order + 1)), mp.mpf(0))
                inverse = mp.mpf(1) / 24 + (w0 + delta) ** 2 / (4 * A)
                approximations.append({"order": order,
                    "forward_relative_error": mp.nstr(forward / y - 1, 26),
                    "inverse_real_index_error": mp.nstr(inverse - n, 26)})
            rows.append({"kind": kind, "k": k, "b": b, "n": n, "exact_y": str(y),
                "threshold_at_y": threshold,
                "exact_previous": str(exact[n - 1]), "exact_next": str(exact[n + 1]),
                "threshold_verification": "first index with X(i)>=y scanned exactly over 0<=i<=n; adjacent counts also checked",
                "approximations": approximations})
    data = metadata() | {"status": "NON-CERTIFIED numerical diagnostics",
        "precision_decimal_digits": mp.mp.dps, "mpmath_version": mp.__version__,
        "error_conventions": {"forward": "approximation/X(n)-1", "inverse": "x_order(X(n))-n"},
        "note": "80-digit arithmetic is not a certified error bound. Orders are fixed truncations, not convergence guarantees. Exact threshold checks do not certify the asymptotic inverse.",
        "rows": rows}
    return {"results/diagnostics.json": dumps(data),
            "tables/forward_table.tex": diagnostic_table(rows, "forward", mp),
            "tables/inverse_table.tex": diagnostic_table(rows, "inverse", mp)}


def tex_number(value, mp):
    number = mp.mpf(value)
    if not number:
        return "0"
    exponent = int(mp.floor(mp.log10(abs(number))))
    mantissa = number / mp.power(10, exponent)
    return mp.nstr(mantissa, 4, strip_zeros=False) + r"\!\times\!10^{" + str(exponent) + "}"


def diagnostic_table(rows, which, mp):
    forward = which == "forward"
    caption = ("Forward relative error $\\mathcal A_R(n)/X(n)-1$ at fixed truncation orders. " if forward else
               "Inverse real-index error $x_M(X(n))-n$; order zero is the Lambert core. ")
    caption += "These 80-digit mpmath evaluations are non-certified diagnostics, not error bounds."
    label = "tab:forward-diagnostics" if forward else "tab:inverse-diagnostics"
    result = ["% Generated by code/reproduce.py --diagnostics; do not edit.",
              r"\begin{table}[htbp]", r"\centering", r"\small", r"\setlength{\tabcolsep}{4pt}",
              r"\begin{tabular}{ccr|rrrrr}", r"\hline",
              r"$X$ & $(k,b)$ & $n$ & $0$ & $1$ & $2$ & $3$ & $6$ \\", r"\hline"]
    key = "forward_relative_error" if forward else "inverse_real_index_error"
    for row in rows:
        errors = ["$" + tex_number(v[key], mp) + "$" for v in row["approximations"]]
        result.append(f"${row['kind']}$ & $({row['k']},{row['b']})$ & {row['n']} & " + " & ".join(errors) + r" \\")
    result += [r"\hline", r"\end{tabular}", r"\caption{" + caption + "}",
               r"\label{" + label + "}", r"\end{table}", ""]
    return "\n".join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact", action="store_true", help="standard-library finite checks and exact coefficients")
    parser.add_argument("--diagnostics", action="store_true", help="optional 80-digit mpmath diagnostics")
    destination = parser.add_mutually_exclusive_group()
    destination.add_argument("--write", action="store_true", help="replace author baselines in code/results and ../tables")
    destination.add_argument("--out", type=Path, help="write fresh results/ and tables/ beneath this directory")
    destination.add_argument("--check", action="store_true", help="compare fresh bytes against saved package baselines")
    args = parser.parse_args()
    if not args.exact and not args.diagnostics:
        args.exact = True
    outputs = {}
    if args.exact:
        outputs.update(exact_outputs())
    if args.diagnostics:
        outputs.update(diagnostics_outputs())
    for name, content in outputs.items():
        subdir, filename = name.split("/", 1)
        baseline = (HERE if subdir == "results" else HERE.parent) / subdir / filename
        if args.check:
            if not baseline.is_file() or baseline.read_bytes() != content.encode("utf-8"):
                raise RuntimeError("baseline mismatch or missing file: " + str(baseline))
        elif args.write or args.out is not None:
            target = baseline if args.write else args.out / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content.encode("utf-8"))
    print(dumps({"status": "PASS", "exact": args.exact, "diagnostics": args.diagnostics,
                 "mode": "check" if args.check else "write" if args.write else "out" if args.out is not None else "read-only",
                 "files": sorted(outputs)}), end="")


if __name__ == "__main__":
    main()
