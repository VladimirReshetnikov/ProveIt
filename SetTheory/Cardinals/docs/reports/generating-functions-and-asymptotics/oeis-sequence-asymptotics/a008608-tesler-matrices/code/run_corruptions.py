#!/usr/bin/env python3
"""Run positive controls and mutation tests as separate Python processes.

The runner itself exits nonzero if a baseline fails, a corruption is accepted,
a corruption fails for the wrong reason, or a process times out. Both normal
and -O interpreters are tested. Temporary inputs stay beneath this directory.
"""
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
NAME = "rational_four_triangles"


class CorruptionTestError(Exception):
    pass


def need(condition, message):
    if not condition:
        raise CorruptionTestError(message)


def cell(entries, a, b):
    matches = [item for item in entries if item["a"] == a and item["b"] == b]
    need(len(matches) == 1, f"mutation setup cell {(a, b)} is not unique")
    return matches[0]


def add_value(entries, a, b, amount):
    target = cell(entries, a, b)
    target["value"] = str(Fraction(target["value"]) + amount)


def mutations(fixtures, expected):
    """Yield name, altered fixtures text, altered expected text, error code."""
    def case(name, code, mutate):
        f, e = deepcopy(fixtures), deepcopy(expected)
        mutate(f, e)
        return name, json.dumps(f), json.dumps(e), code

    yield case("bad_cut_load", "CUT", lambda f, e: add_value(f["fixtures"][0]["completed"], 1, 1, 1))
    yield case("bad_expected_netflow", "NETFLOW", lambda f, e: e["fixtures"][NAME]["netflow"].__setitem__(1, "2"))
    yield case("negative_edge", "NONNEGATIVE", lambda f, e: cell(f["fixtures"][0]["completed"], 1, 1).__setitem__("value", "-1"))
    yield case("row_margin_inconsistency", "ROW_MARGIN", lambda f, e: e["fixtures"][NAME]["rows"].__setitem__(0, "2"))
    yield case("column_margin_inconsistency", "COLUMN_MARGIN", lambda f, e: e["fixtures"][NAME]["columns"].__setitem__(0, "2"))
    yield case("missing_cell", "SCHEMA", lambda f, e: f["fixtures"][0]["completed"].pop())
    yield case("duplicate_cell", "SCHEMA", lambda f, e: f["fixtures"][0]["completed"].append(deepcopy(f["fixtures"][0]["completed"][0])))
    yield case("invalid_fraction_denominator", "RATIONAL", lambda f, e: f["fixtures"][0]["q"][0].__setitem__("value", "1/0"))
    yield case("noncanonical_fraction", "RATIONAL", lambda f, e: f["fixtures"][0]["q"][0].__setitem__("value", "2/4"))
    yield case("floating_point_rational", "RATIONAL", lambda f, e: f["fixtures"][0]["q"][0].__setitem__("value", 0.0))
    yield case("boolean_dimension", "SCHEMA", lambda f, e: f["fixtures"][0].__setitem__("n", True))
    yield case("unknown_fixture_field", "SCHEMA", lambda f, e: f["fixtures"][0].__setitem__("silently_ignored", 1))
    yield case("invalid_support", "SCHEMA", lambda f, e: f["fixtures"][0]["completed"][0].__setitem__("b", 0))
    yield case("altered_expected_count", "EXPECTED_COUNT", lambda f, e: e["small_counts"].__setitem__("3", 8))
    yield case("missing_expected_count", "SCHEMA", lambda f, e: e["small_counts"].pop("7"))
    yield case("missing_fixture", "FIXTURE_COVERAGE", lambda f, e: f["fixtures"].pop())
    yield case("cutoff_violation", "CUTOFF", lambda f, e: cell(f["fixtures"][0]["q"], 1, 1).__setitem__("value", "1"))
    yield case("bad_expected_q_load", "Q_CUT", lambda f, e: e["fixtures"][NAME]["q_cut_loads"].__setitem__(0, "1"))

    def overload(f, e):
        add_value(f["fixtures"][0]["q"], 12, 12, 100)
        old = Fraction(e["fixtures"][NAME]["q_cut_loads"][11])
        e["fixtures"][NAME]["q_cut_loads"][11] = str(old + 100)
    yield case("q_exceeds_cut_capacity", "Q_FEASIBILITY", overload)

    def other_feasible_completion(f, e):
        entries = f["fixtures"][0]["completed"]
        add_value(entries, 8, 9, -Fraction(1, 4))
        add_value(entries, 8, 8, Fraction(1, 4))
        add_value(entries, 9, 9, Fraction(1, 4))
    yield case("wrong_but_feasible_completion", "COMPLETION", other_feasible_completion)
    yield case("triangle_coefficient_perturbation", "TRIANGLE_CUT",
               lambda f, e: cell(f["fixtures"][0]["triangles"][0]["changes"], 8, 9).__setitem__("value", "-2"))

    def cross_coupled_triangle(f, e):
        # Add one third of the NEXT valid triangle to the first rule. Cuts
        # and netflow are still exactly preserved; only independence fails.
        first = f["fixtures"][0]["triangles"][0]["changes"]
        second = f["fixtures"][0]["triangles"][1]["changes"]
        changes = {(item["a"], item["b"]): Fraction(item["value"]) for item in first}
        for item in second:
            key = item["a"], item["b"]
            changes[key] = changes.get(key, Fraction(0)) + Fraction(item["value"]) / 3
        first[:] = [{"a": a, "b": b, "value": str(value)} for (a, b), value in sorted(changes.items())]
    yield case("cut_preserving_triangle_cross_coupling", "TRIANGLE_INDEPENDENCE", cross_coupled_triangle)
    yield case("missing_triangle", "TRIANGLE_COVERAGE", lambda f, e: f["fixtures"][0]["triangles"].pop())
    yield case("altered_integer_choice", "INTEGER_CHOICES", lambda f, e: e["fixtures"][NAME]["triangle_choices"]["8"].__setitem__(0, 4))
    yield case("altered_choice_product", "CHOICE_PRODUCT", lambda f, e: e["fixtures"][NAME].__setitem__("choice_product", 37))
    yield case("altered_margin_digest", "MARGIN_DIGEST", lambda f, e: e["fixtures"][NAME].__setitem__("margin_vector_sha256", "0" * 64))
    yield case("unknown_expected_field", "SCHEMA", lambda f, e: e.__setitem__("silently_ignored", 1))
    ftext, etext = json.dumps(fixtures), json.dumps(expected)
    yield "malformed_json", "{bad json", etext, "INPUT"
    yield "duplicate_json_object_key", ftext.replace('"schema_version": 1', '"schema_version": 1, "schema_version": 1', 1), etext, "SCHEMA"
    yield "nonfinite_json_constant", ftext.replace('"schema_version": 1', '"schema_version": NaN', 1), etext, "SCHEMA"
    yield "empty_input", "", etext, "INPUT"


def execute(mode, fixtures, expected):
    command = [sys.executable] + (["-O"] if mode == "optimized" else []) + [str(ROOT / "verify_exact.py"),
               "--fixtures", str(fixtures), "--expected", str(expected)]
    try:
        return subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=180)
    except subprocess.TimeoutExpired as exc:
        raise CorruptionTestError(f"{mode}: verifier timed out, not an acceptable rejection") from exc


def main():
    lines, records = [], []
    timestamp = datetime.now(timezone.utc).isoformat()
    try:
        fixtures = json.loads((ROOT / "rational_fixtures.json").read_text(encoding="utf-8"))
        expected = json.loads((ROOT / "expected_checks.json").read_text(encoding="utf-8"))
        cases = list(mutations(fixtures, expected))
        need(len(cases) == 31, "corruption coverage changed without updating its required count")
        need(len({item[0] for item in cases}) == len(cases), "duplicate corruption names")
        for mode in ("normal", "optimized"):
            baseline = execute(mode, ROOT / "rational_fixtures.json", ROOT / "expected_checks.json")
            need(baseline.returncode == 0, f"{mode} positive control failed: {baseline.stderr}")
            parsed = json.loads(baseline.stdout)
            need(parsed.get("status") == "PASS", f"{mode} positive control did not return PASS")
            need(parsed.get("python_optimization") == (mode == "optimized"), f"{mode} optimization mode mismatch")
            (ROOT / f"verification_{mode}.json").write_text(baseline.stdout, encoding="utf-8")
            lines.append(f"PASS {mode}: unmodified suite exited 0")
            with tempfile.TemporaryDirectory(prefix="corruption_inputs_", dir=ROOT) as directory:
                fp, ep = Path(directory) / "fixtures.json", Path(directory) / "expected.json"
                for name, ftext, etext, code in cases:
                    fp.write_text(ftext, encoding="utf-8")
                    ep.write_text(etext, encoding="utf-8")
                    run = execute(mode, fp, ep)
                    need(run.returncode != 0, f"{mode}/{name}: corruption was accepted")
                    need('"status": "PASS"' not in run.stdout, f"{mode}/{name}: emitted PASS for corruption")
                    need(f"VerificationError: {code}:" in run.stderr,
                         f"{mode}/{name}: wrong failure reason: {run.stderr.strip()}")
                    records.append({"mode": mode, "mutation": name, "exit_code": run.returncode,
                                    "expected_error_code": code, "stderr": run.stderr.strip()})
                    lines.append(f"PASS {mode}/{name}: rejected with exit {run.returncode}, {code}")
        result = {"status": "PASS", "timestamp_utc": timestamp, "python": sys.version,
                  "positive_controls": 2, "mutations_per_mode": len(cases), "rejected_mutations": len(records),
                  "records": records}
        (ROOT / "corruption_results.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        lines.append(f"PASS: 2 positive controls and {len(records)} fail-closed corruption rejections")
    except Exception as exc:
        lines.append(f"FAIL {type(exc).__name__}: {exc}")
        (ROOT / "corruption_run.log").write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(lines[-1], file=sys.stderr)
        return 1
    (ROOT / "corruption_run.log").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(lines[-1])
    return 0


if __name__ == "__main__":
    sys.exit(main())
