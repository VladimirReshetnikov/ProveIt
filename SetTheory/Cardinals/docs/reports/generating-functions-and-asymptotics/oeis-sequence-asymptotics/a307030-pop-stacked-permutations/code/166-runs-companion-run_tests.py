#!/usr/bin/env python3
"""Standard-library regression tests; JSON stdout only, no files or subprocesses."""

import io
import json
import sys
from contextlib import redirect_stdout
from fractions import Fraction

sys.dont_write_bytecode = True

import run_checks
import run_filtration
import run_polynomials as rp
import run_slopes as rs


_EXPECTED_ROWS = [
    [1], [0, 1], [0, 1], [0, 1, 2], [0, 1, 8, 2],
    [0, 1, 22, 26], [0, 1, 52, 168, 42], [0, 1, 114, 804, 692, 42],
    [0, 1, 240, 3270, 6500, 1866], [0, 1, 494, 12054, 46304, 34078, 3060],
]


def _raises(exception, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except exception:
        return
    raise rp.CheckFailure(f"expected {exception.__name__} from {function.__name__}")


def test_checks_remain_active():
    _raises(rp.CheckFailure, rp.require, False, "intentional failure")
    _raises(rp.CheckFailure, rp._divide_by_4u_minus_1, [Fraction(1)])
    rp.require(rp._divide_by_4u_minus_1([Fraction(-1), Fraction(4)]) == [1],
               "exact polynomial division failed")


def test_bounds_and_input_validation():
    for function in (rp.egf_run_polynomials, rp.endpoint_run_polynomials):
        for value in (-1, 41, 1.0, True, "4"):
            _raises(ValueError, function, value)
    for value in (-1, 10, False):
        _raises(ValueError, rp.literal_run_polynomials, value)
    for value in (0, 13, True):
        _raises(ValueError, run_filtration.filtered_run_coefficients, value)
    _raises(ValueError, rp.check_run_polynomials, 2, 3)
    _raises(ValueError, rp.pop_stack_image, [1, 1])
    _raises(ValueError, rp.pop_stack_image, [True])
    _raises(ValueError, rp.pop_stack_image, list(range(1, 11)))
    _raises(ValueError, rp.pop_stack_image, iter([1]))
    _raises(ValueError, rp.fixed_run_numerator, 6)
    _raises(ValueError, rp.fixed_run_denominator, 0)
    _raises(ValueError, run_filtration.check_filtration, 1, 2, [[1]])
    _raises(ValueError, rp.check_published_fixed_runs, [[0]])


def test_empty_and_literal_map():
    for function in (rp.egf_run_polynomials, rp.endpoint_run_polynomials,
                     rp.literal_run_polynomials):
        rp.require(function(0) == [[1]], f"{function.__name__} mishandles n=0")
    rp.require(rp.pop_stack_image([]) == (), "empty pop-stack image failed")
    rp.require(rp.pop_stack_image([3, 2, 1]) == (1, 2, 3), "decreasing input failed")
    rp.require(rp.pop_stack_image([3, 1, 2]) == (1, 3, 2), "flush transition failed")
    rp.require(rp.pop_stack_image([1, 2, 3]) == (1, 2, 3), "increasing input failed")


def test_complete_polynomial_paths():
    result = rp.check_run_polynomials(12, 7, True)
    rp.require(result["run_polynomials"][:10] == _EXPECTED_ROWS,
               "known complete-row regression fixture differs")
    rp.require(result["published_fixed_runs"]["coefficient_equations_checked"] == 65,
               "incorrect fixed-run coefficient check count")
    rp.require(result["literal_run_polynomials"] == _EXPECTED_ROWS[:8],
               "literal-image regression fixture differs")
    rp.require(result["run_polynomials"] == rp.egf_run_polynomials(12),
               "a second EGF call has changed its result")


def test_fixed_fixtures_and_mutation_detection():
    rows = [row.copy() for row in _EXPECTED_ROWS]
    rows[5][2] += 1
    _raises(rp.CheckFailure, rp.check_published_fixed_runs, rows)
    numerator = rp.fixed_run_numerator(5)
    numerator[7] = -1
    rp.require(rp.fixed_run_numerator(5)[7] == 42,
               "fixture escaped by mutable reference")
    rp.require(rp.fixed_run_denominator(3) == [1, -10, 40, -82, 91, -52, 12],
               "denominator product fixture differs")


def test_optional_filtered_examples():
    coefficients = run_filtration.filtered_run_coefficients(1)
    rp.require(coefficients[1] == {(0, 0): Fraction(-1), (1, 0): Fraction(1)},
               "k=1 filtered polynomial is not exp(z)-1")
    result = run_filtration.check_filtration(5, 12, include_data=True)
    for k in range(1, 6):
        rp.require(result["ordinary_numerators"][str(k)] == rp.fixed_run_numerator(k),
                   f"filtered numerator differs from published fixture k={k}")
    rp.require(result["coefficient_comparisons"] == 65,
               "wrong number of filtered-series coefficient comparisons")
    rows = rp.egf_run_polynomials(6)
    rows[4][2] += 1
    _raises(rp.CheckFailure, run_filtration.check_filtration, 2, 6, rows)


def test_interval_primitives_and_outward_rounding():
    f = Fraction
    rp.require(rs._exp_point(f(0)) == (f(1), f(1)), "exp(0) enclosure differs")
    rp.require(rs._trig_point(f(0), True) == (f(0), f(0)), "sin(0) differs")
    rp.require(rs._trig_point(f(0), False) == (f(1), f(1)), "cos(0) differs")
    low, high = rs._sqrt_point(f(2))
    rp.require(low**2 <= 2 <= high**2, "sqrt(2) bracket misses true root")
    rp.require(rs._multiply((f(-2), f(-1)), (f(3), f(5))) == (f(-10), f(-3)),
               "signed interval multiplication failed")
    rp.require(rs._print_interval((f(-1, 3), f(1, 3)), 3) == ["-0.334", "0.334"],
               "decimal conversion was not outward-rounded")
    _raises(rp.CheckFailure, rs._divide, rs._fixed(1), (f(-1), f(1)))
    _raises(rp.CheckFailure, rs._trig_point, f(2), True)
    _raises(rp.CheckFailure, rs._sin_interval, (f(-1), f(0)))
    _raises(rp.CheckFailure, rs._cos_interval, (f(1), f(0)))
    _raises(rp.CheckFailure, rs._sqrt_point, f(-1))


def test_rational_slope_certificate():
    result = rs.certify_slopes()
    rp.require(result["rho_upper_less_than_6_over_5"]
               and result["exp_6_over_5_upper_less_than_4"]
               and Fraction(result["exp_6_over_5_bracket"][1]) < 4,
               "rho < log(4) rational bridge failed")
    rp.require(result["passed"] and result["variance_numerator_positive"],
               "slope certificate failed")
    rp.require(Fraction(result["D_at_rho_lower"][0]) > 0,
               "printed lower-endpoint sign is not positive")
    rp.require(Fraction(result["D_at_rho_upper"][1]) < 0,
               "printed upper-endpoint sign is not negative")
    rp.require(Fraction(result["variance_slope_bracket"][0]) > 0,
               "printed variance slope is not positive")


def _cli(arguments):
    captured = io.StringIO()
    with redirect_stdout(captured):
        status = run_checks.main(arguments)
    return status, json.loads(captured.getvalue()), captured.getvalue()


def test_cli_json_and_invalid_arguments():
    for arguments in (["--bad-flag"], ["coefficients", "--n", "41"],
                      ["all", "--filtration", "13"],
                      ["slopes", "--n", "999"],
                      ["coefficients", "--filtration", "1"],
                      ["coefficients", "--n", "2", "--literal", "3"]):
        status, output, _ = _cli(arguments)
        rp.require(status == 2 and output["error_type"] == "invalid_input",
                   f"CLI did not reject {arguments!r} as JSON")
    status, output, _ = _cli(["--help"])
    rp.require(status == 0 and "usage" in output, "JSON help failed")
    args = ["coefficients", "--n", "6", "--literal", "6", "--include-data"]
    status, output, text = _cli(args)
    rp.require(status == 0 and output["passed"], "CLI success failed")
    rp.require(output["coefficients"]["run_polynomials"] == _EXPECTED_ROWS[:7],
               "CLI included wrong polynomial data")
    rp.require(_cli(args)[2] == text, "CLI stdout is nondeterministic")
    for args, expected in (
        (["slopes"], "slopes"),
        (["filtration", "--n", "6", "--filtration", "3"], "filtration"),
        (["all", "--n", "6", "--literal", "6", "--filtration", "3"], "filtration"),
    ):
        status, output, _ = _cli(args)
        rp.require(status == 0 and output[expected]["passed"],
                   f"CLI command path failed: {args!r}")
    original = run_checks.check_run_polynomials
    def fail_check(*args, **kwargs):
        raise rp.CheckFailure("intentional CLI check failure")
    try:
        run_checks.check_run_polynomials = fail_check
        status, output, _ = _cli(["coefficients"])
        rp.require(status == 1 and output["error_type"] == "check_failed",
                   "CLI check failure did not produce JSON with status 1")
    finally:
        run_checks.check_run_polynomials = original


def main():
    tests = [test_checks_remain_active, test_bounds_and_input_validation,
             test_empty_and_literal_map, test_complete_polynomial_paths,
             test_fixed_fixtures_and_mutation_detection,
             test_optional_filtered_examples,
             test_interval_primitives_and_outward_rounding,
             test_rational_slope_certificate, test_cli_json_and_invalid_arguments]
    passed = []
    for test in tests:
        try:
            test()
        except Exception as error:
            print(json.dumps({"passed": False, "failed_test": test.__name__,
                              "error_type": type(error).__name__, "error": str(error),
                              "tests_completed": passed}, indent=2, sort_keys=True))
            return 1
        passed.append(test.__name__)
    print(json.dumps({"passed": True, "tests_passed": len(passed),
                      "tests": passed, "normal_and_optimized_checks": "same explicit check code"},
                     indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
