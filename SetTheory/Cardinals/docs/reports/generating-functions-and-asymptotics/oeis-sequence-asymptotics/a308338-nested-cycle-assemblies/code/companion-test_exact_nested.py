"""Explicit regression checks; checks are not removed by python -O."""
import sys
sys.dont_write_bytecode = True
import contextlib
import copy
import io
import json
from fractions import Fraction

import exact_nested as e
import verify as v


def must_raise(exception, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except exception:
        return
    raise e.CheckFailure(f"expected {exception.__name__} from {function.__name__}")


def run_tests():
    groups = []
    expected = [[1], [0, 1], [0, 1, 1], [0, 5, 3, 1],
                [0, 14, 23, 6, 1], [0, 74, 120, 65, 10, 1]]
    for function in (e.nested_triangle, e.rational_power_triangle, e.literal_nested_triangle):
        e.check(function(5) == expected, f"small rows: {function.__name__}")
    e.check(e.component_counts(5) == [1, 1, 1, 5, 14, 74], "small component counts")
    e.check(e.nested_counts(5) == [1, 1, 2, 9, 44, 270], "small nested counts")
    groups.append("small exact rows and counts")

    for function in (e.component_counts, e.nested_counts, e.nested_triangle,
                     e.rational_component_series, e.rational_egf_counts,
                     e.rational_power_triangle, e.literal_nested_triangle, e.exact_moments):
        for bad in (-1, 101, True, False, 1.0, "5", None):
            must_raise(ValueError, function, bad)
    must_raise(ValueError, e.rational_power_triangle, 31)
    must_raise(ValueError, e.literal_nested_triangle, 8)
    must_raise(ValueError, v.verify, n=4, power_n=5, literal_n=4)
    must_raise(ValueError, v.verify, n=4, power_n=4, literal_n=5)
    must_raise(ValueError, v.verify, n=4, power_n=4, literal_n=4, include_data=1)
    groups.append("bounds and type rejection")

    must_raise(e.CheckFailure, e.check, False, "deliberately false identity")
    must_raise(e.CheckFailure, e._integer, Fraction(1, 2), "deliberately nonintegral")
    fixtures = copy.deepcopy(v.read_fixtures())
    fixtures["sequences"]["A308338"]["terms"][3] = "8"
    must_raise(e.CheckFailure, v.verify, n=5, power_n=5, literal_n=5, fixtures=fixtures)
    groups.append("deliberate mathematical failures remain active")

    for y, expected_inverse in ((1, 0), (2, 2), (3, 3), (9, 3), (10, 4), (44, 4), (45, 5), (270, 5)):
        e.check(e.exact_inverse(y, 5) == expected_inverse, f"inverse threshold {y}")
    e.check(e.exact_inverse(1, 0) == 0, "inverse at empty extension")
    for y in (0, -1, True, 1.0, "10"):
        must_raise(ValueError, e.exact_inverse, y)
    must_raise(ValueError, e.exact_inverse, 271, 5)
    must_raise(ValueError, e.exact_inverse, 2, 0)
    groups.append("exact inverse equality and between-threshold cases")

    e.check(e.exact_moments(0) == {"mean": Fraction(0), "variance": Fraction(0)}, "empty moments")
    e.check(e.exact_moments(2) == {"mean": Fraction(3, 2), "variance": Fraction(1, 4)}, "size-two moments")
    e.check(e.exact_moments(5) == {"mean": Fraction(277, 135), "variance": Fraction(12641, 18225)}, "size-five moments")
    groups.append("exact rational moments")

    p = e.rational_component_series(5)
    e.check(p == [Fraction(1), Fraction(1), Fraction(1,2), Fraction(5,6), Fraction(7,12), Fraction(37,60)],
            "rational component normalization")
    rows = e.nested_triangle(3)
    rows[1][1] = -17
    e.check(e.nested_triangle(3)[1] == [0,1], "returned arrays are fresh")
    groups.append("normalization and fresh return values")

    for args, status, label in ((["--n", "0"], 0, "zero"),
                                (["--n", "101"], 2, "large bound"),
                                (["--n", "5", "--power-n", "6"], 2, "incompatible bounds"),
                                (["--n", "5", "--include-data"], 0, "included arrays")):
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured):
            actual_status = v.main(args)
        e.check(actual_status == status, f"CLI exit status: {label}")
        payload = json.loads(captured.getvalue())
        e.check(payload["status"] == ("passed" if status == 0 else "invalid-input"), f"CLI JSON: {label}")
        if label == "included arrays":
            e.check(payload["data"]["nested"] == ["1","1","2","9","44","270"], "CLI exact arrays")
    groups.append("CLI success and failure contracts")

    result = v.verify()
    e.check(result["comparisons"]["complete_integer_triangle_entries"] == 5151, "full triangle scope")
    e.check(all(item["all_available_checked"] for item in result["published_fixtures"].values()), "all published terms checked")
    groups.append("full bounded independent verification")
    return {"schema": "report167-regression-tests-v1", "status": "passed", "groups": groups,
            "number_of_groups": len(groups), "safety_checks": "ordinary conditionals, active under -O"}


if __name__ == "__main__":
    try:
        result = run_tests()
    except Exception as error:
        print(json.dumps({"status": "failed", "error": str(error)}, sort_keys=True))
        raise SystemExit(1)
    print(json.dumps(result, indent=2, sort_keys=True))
