#!/usr/bin/env python3
"""Bounded deliberate-failure regression suite. Run normally and with python -O."""
from __future__ import annotations

import argparse
import contextlib
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile

import companion as c


def expect_error(exception, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except exception:
        return
    raise RuntimeError(f"expected {exception.__name__}: {function.__name__}")


def run_tests():
    passed = []

    def record(name, function):
        function()
        passed.append(name)

    record("integer_division_success", lambda: c.require(c.exact_div(42, 7, "test") == 6, "division result"))
    record("nondivisible_integer_rejected", lambda: expect_error(c.ValidationError, c.exact_div, 43, 7, "test"))
    record("zero_divisor_rejected", lambda: expect_error(c.ValidationError, c.exact_div, 1, 0, "test"))
    record("float_dividend_rejected", lambda: expect_error(c.ValidationError, c.exact_div, 4.0, 2, "test"))
    for value in [0, -1, 1001, True, 1.5]:
        record(f"count_bound_rejects_{value}", lambda value=value: expect_error(c.ValidationError, c.exact_results, value))
    record("lagrange_limit_rejected", lambda: expect_error(c.ValidationError, c.inverse_lagrange, "general", 82))
    record("unknown_case_rejected", lambda: expect_error(c.ValidationError, c.inverse_ode, "unknown", 10))
    result = c.exact_results(n=80)
    record("independent_exact_prefixes_and_residuals", lambda: c.require(result["oeis_prefix_terms_checked"] ==
            {"A277493": 5, "A324312": 22, "A324314": 20}, "fixture coverage"))
    r = c.inverse_ode("general", 20)
    r[-1] += 1
    record("corrupt_inverse_residual_rejected", lambda: expect_error(c.ValidationError, c.check_ode_residual, "general", r))
    general = [int(v) for v in result["cases"]["general"]["counts"]]
    quartic = [int(v) for v in result["cases"]["quartic"]["counts"]]
    general[1] += 1
    record("incorrect_oeis_term_rejected", lambda: expect_error(c.ValidationError, c.check_oeis, general, quartic))
    record("Q0_Q5_and_U0_U3_symbolic_checks", c.symbolic_results)
    diagnostic = c.diagnostic_results(n=30, digits=60, prefix=20)
    record("lambert_recurrence_lagrange_prefix", lambda: c.require(
        all(v["lagrange_checked_through_m"] == 20 for v in diagnostic["cases"].values()), "Lambert prefix coverage"))
    record("diagnostic_precision_bound", lambda: expect_error(c.ValidationError, c.diagnostic_results, 30, 49))
    record("diagnostic_prefix_bound", lambda: expect_error(c.ValidationError, c.diagnostic_results, 30, 60, 61))
    inverse = c.inverse_results("A277493", "1000", 60)
    record("inverse_disclaims_integer_rounding", lambda: c.require("no integer threshold" in inverse["interpretation"], "inverse disclaimer"))
    for value in ["nan", "inf", "9", "1000000001", "-100", "3" * 101]:
        record(f"invalid_log_y_rejected_{value[:12]}", lambda value=value: expect_error(c.ValidationError, c.inverse_results, "A324312", value))
    with tempfile.TemporaryDirectory(prefix="report171-tests-") as tmp:
        folder = Path(tmp)
        target = folder / "existing.json"
        target.write_text("preserve me\n")
        record("exclusive_writer_no_clobber", lambda: expect_error(FileExistsError, c.write_new, target, b"replacement"))
        c.require(target.read_text() == "preserve me\n", "existing output was altered")
        link = folder / "existing-link.json"
        link.symlink_to(target)
        record("symlink_no_clobber", lambda: expect_error(FileExistsError, c.write_new, link, b"replacement"))
        copied = folder / "fixtures"
        shutil.copytree(c.FIXTURES, copied)
        with (copied / "oeis_prefixes.json").open("a") as stream:
            stream.write(" ")
        record("fixture_hash_tampering_rejected", lambda: expect_error(c.ValidationError, c.check_fixtures, copied))
        with contextlib.redirect_stderr(io.StringIO()):
            record("CLI_bound_error_nonzero", lambda: c.require(c.main(["exact", "--n", "1001"]) == 2, "CLI failure status"))
            record("CLI_no_clobber_nonzero", lambda: c.require(c.main(["exact", "--output", str(target)]) == 2, "CLI clobber status"))
    return {"schema": "Report171-tests-v1", "optimization_level": sys.flags.optimize,
            "status": "passed", "count": len(passed), "tests": passed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output and (args.output.exists() or args.output.is_symlink()):
        parser.error("refusing existing output")
    data = c.json_bytes(run_tests())
    if args.output:
        c.write_new(args.output, data)
    else:
        sys.stdout.buffer.write(data)


if __name__ == "__main__":
    main()
