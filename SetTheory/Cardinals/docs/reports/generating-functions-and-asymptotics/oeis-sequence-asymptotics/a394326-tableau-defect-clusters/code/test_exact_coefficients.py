#!/usr/bin/env python3
"""Run deterministic exact-coefficient tests, including under python -O.

Usage from any working directory:
    python /path/to/code/test_exact_coefficients.py
    python -O /path/to/code/test_exact_coefficients.py

No test uses an assert statement. Failed checks always raise an exception.
The saved fixture and generator are located relative to this script; there
are no dependencies on the research workspace or its original probe files.
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Callable

from exact_coefficients import (
    SOURCE_PREFIX,
    VerificationError,
    check_source_prefix,
    cluster_from_first_returns,
    generate,
    independent_tableau_check,
    polynomial_product,
    primitive_gap_paths,
    require_equal,
    tableau_inversion_polynomial,
)


def require_raises(exception: type[Exception], action: Callable[[], object], label: str) -> None:
    try:
        action()
    except exception:
        return
    raise VerificationError(f"{label}: expected {exception.__name__}")


def main() -> int:
    code_dir = Path(__file__).resolve().parent
    fixture_path = code_dir.parent / "data" / "exact_coefficients.json"
    fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
    baseline = generate(65)
    require_equal(fixture, baseline, "saved JSON regeneration")
    require_equal(baseline["checks"]["source_prefix_terms_checked"], 40, "full source check")
    require_equal(baseline["a"][1:41], list(SOURCE_PREFIX), "40 source values")
    require_equal(baseline["a"][65], 7051878934360, "extension endpoint a_65")
    require_equal(baseline["I"][65], 864593532752424451766740, "primitive endpoint I_65")
    tests = ["saved_fixture_regeneration", "40_source_terms", "extension_endpoints"]

    for weight in (0, 1, 2, 4, 8, 40, 70):
        result = generate(weight)
        common = min(weight, 65) + 1
        require_equal(result["a"][:common], baseline["a"][:common], f"a prefix at cutoff {weight}")
        require_equal(result["I"][:common], baseline["I"][:common], f"I prefix at cutoff {weight}")
        require_equal(len(result["a"]), weight + 1, f"array length at cutoff {weight}")
        require_equal(result["checks"]["source_prefix_terms_checked"], min(weight, 40), "source check length")
    tests.append("cutoff_consistency_0_1_2_4_8_40_70")

    primitive, rows = primitive_gap_paths(8)
    require_equal(rows[1], [1] + [0] * 8, "size-one primitive")
    require_equal(rows[2], [0, 1, 2, 1, 0, 0, 0, 0, 0], "size-two primitive")
    require_equal(tableau_inversion_polynomial(2), [1, 2, 1, 1], "size-two inversion distribution")
    independent = independent_tableau_check(8, baseline["a"], rows)
    require_equal(independent["a"], [0, 1, 2, 1, 1, 3, 5, 6, 7], "independent prefix")
    require_equal(
        independent["tableau_counts_by_size"],
        [1, 1, 5, 42, 462, 6006, 87516, 1385670, 23371634, 414315330],
        "hook-length totals through size nine",
    )
    require_equal(
        polynomial_product(primitive, [1] + [-x for x in baseline["a"][1:9]], 8),
        [1] + [0] * 8,
        "independent reciprocal identity",
    )
    tests.extend(["small_primitive_and_inversion_polynomials", "independent_tableaux_and_spans"])

    bad_source = baseline["a"].copy()
    bad_source[40] += 1
    require_raises(VerificationError, lambda: check_source_prefix(bad_source), "source corruption")
    bad_rows = [row.copy() for row in rows]
    bad_rows[2][1] += 1
    require_raises(
        VerificationError,
        lambda: independent_tableau_check(8, baseline["a"], bad_rows),
        "primitive corruption",
    )
    bad_cluster = baseline["a"].copy()
    bad_cluster[8] += 1
    require_raises(
        VerificationError,
        lambda: independent_tableau_check(8, bad_cluster, rows),
        "span-extraction corruption",
    )
    tests.append("deliberate_corruption_detected")

    for value in (-1, 1.5, True, "8"):
        require_raises(ValueError, lambda value=value: generate(value), f"bad cutoff {value!r}")
    for invalid_series in ([], [0, 1], [2, 1], [1, 0.5]):
        require_raises(
            ValueError,
            lambda invalid_series=invalid_series: cluster_from_first_returns(invalid_series),
            "invalid reciprocal input",
        )
    tests.append("invalid_inputs_rejected")

    generator = code_dir / "exact_coefficients.py"
    expected_bytes = fixture_path.read_bytes()
    with tempfile.TemporaryDirectory(prefix="exact-coefficients-test-") as temporary:
        directory = Path(temporary)
        for mode in ([], ["-O"]):
            output = directory / ("optimized.json" if mode else "normal.json")
            command = [sys.executable, '-I', '-S', '-B', *mode, str(generator), "--max-weight", "65", "--output", str(output)]
            completed = subprocess.run(command, cwd=directory, capture_output=True, text=True, check=False)
            require_equal(completed.returncode, 0, f"CLI {mode}: {completed.stderr}")
            require_equal(completed.stdout, "", "file-output CLI has clean stdout")
            require_equal(output.read_bytes(), expected_bytes, f"bytewise CLI regeneration {mode}")
        stdout_run = subprocess.run(
            [sys.executable, "-I", "-S", "-B", "-O", str(generator), "--max-weight", "0"],
            cwd=directory, capture_output=True, text=True, check=False,
        )
        require_equal(stdout_run.returncode, 0, "stdout CLI")
        require_equal(json.loads(stdout_run.stdout), generate(0), "stdout JSON")
        bad_run = subprocess.run(
            [sys.executable, "-I", "-S", "-B", "-O", str(generator), "--max-weight", "-1"],
            cwd=directory, capture_output=True, text=True, check=False,
        )
        require_equal(bad_run.returncode, 2, "negative CLI cutoff")
    tests.extend(["bytewise_cli_regeneration_normal_and_optimized", "stdout_cli", "invalid_cli_cutoff"])
    print(json.dumps({"status": "passed", "test_count": len(tests), "tests": tests}, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
