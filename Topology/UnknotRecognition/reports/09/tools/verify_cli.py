"""Portable CLI/API smoke verification for the packaged integration.

Run from any directory::

    python /path/to/package/tools/verify_cli.py

The CLI cases execute in fresh processes with PYTHONPATH restricted to the
packaged ``fast`` directory.  The default record is data/cli_validation.json.
This is an integration check, not a repeat of the mathematical test suites.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def run_cli(name, options, expected_exit, expected_status=None, *, timeout=60):
    argv = [sys.executable, "-m", "fastunknot", "recognize", *options]
    env = dict(os.environ, PYTHONPATH=str(ROOT / "fast"))
    started = time.perf_counter()
    process = subprocess.run(argv, cwd=ROOT, env=env, text=True,
                             capture_output=True, timeout=timeout, check=False)
    record = {
        "name": name, "kind": "cli", "command": ["python", *argv[1:]],
        "working_directory": ".", "environment": {"PYTHONPATH": "fast"},
        "expected_exit": expected_exit, "exit_code": process.returncode,
        "seconds": time.perf_counter() - started,
        "stdout": process.stdout, "stderr": process.stderr,
        "checks": [],
    }
    failures = []
    if process.returncode != expected_exit:
        failures.append(f"expected exit {expected_exit}, received {process.returncode}")
    else:
        record["checks"].append("exit code")
    if "Traceback" in process.stdout or "Traceback" in process.stderr:
        failures.append("unexpected traceback")
    else:
        record["checks"].append("no traceback")
    if expected_status is not None:
        try:
            result = json.loads(process.stdout)
        except (TypeError, ValueError) as exc:
            failures.append(f"stdout is not a JSON result: {exc}")
        else:
            record["result"] = result
            record["status"] = result.get("status")
            if result.get("status") != expected_status:
                failures.append(f"expected status {expected_status}, received {result.get('status')}")
            else:
                record["checks"].append("JSON verdict")
            if result.get("quasipolynomial_guarantee") is not False:
                failures.append("result does not explicitly deny a quasi-polynomial guarantee")
            else:
                record["checks"].append("complexity claim")
    record["failures"] = failures
    return record


def add_check(record, label, function):
    try:
        function()
    except Exception as exc:
        record["failures"].append(f"{label}: {type(exc).__name__}: {exc}")
    else:
        record["checks"].append(label)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=str(ROOT / "data" / "cli_validation.json"))
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    cases = []

    def cli(*values, **options):
        record = run_cli(*values, **options, timeout=args.timeout)
        cases.append(record)
        print(record["name"], "exit", record["exit_code"],
              "status", record.get("status", "option error"), flush=True)
        return record

    default = cli("default_conway", ["fast/examples/conway.json"], 0, "KNOTTED")
    add_check(default, "default exact result", lambda: require(
        default["result"]["is_unknot"] is False, "KNOTTED must set is_unknot=false"))

    legacy = cli("legacy_connected_sum", ["fast/examples/conway_sum_2.json", "--legacy-factor"],
                 0, "KNOTTED")

    def legacy_schema():
        evidence = legacy["result"]["evidence"]
        cuts = evidence["connected_sum_cuts"]
        require(isinstance(cuts, list) and len(cuts) == 1, "expected one legacy cut")
        require(len(cuts[0]["cut_edges"]) == 2, "legacy cut must identify two edges")
        require(sorted(cuts[0]["crossings"]) == [11, 11], "legacy split must have two Conway factors")
        require("connected_sum_factorization" not in evidence, "mixed legacy/new schemas")
        require(legacy["result"]["method"].startswith("connected-sum-factor:"),
                "legacy CLI did not decide via a factor")

    add_check(legacy, "legacy factor evidence schema", legacy_schema)

    current = cli("interlacement_connected_sum", ["fast/examples/conway_sum_2.json"], 0, "KNOTTED")

    def interlacement_schema():
        evidence = current["result"]["evidence"]
        certificate = evidence["connected_sum_factorization"]
        require(certificate["algorithm"] == "gauss-interlacement-v1", "unknown certificate version")
        require(sorted(map(len, certificate["crossing_components"])) == [11, 11],
                "expected two Conway crossing components")
        require(len(certificate["interlacement_forest"]) == 20, "expected n-k witness edges")
        require(certificate["original_crossings"] == current["result"]["reduced_crossings"],
                "certificate crossing count disagrees with processed diagram")
        require("connected_sum_cuts" not in evidence, "mixed legacy/new schemas")
        require(current["result"]["method"].startswith("connected-sum-factor:"),
                "new CLI did not decide via a factor")

    add_check(current, "interlacement factor evidence schema", interlacement_schema)

    pointed = cli("forced_pointed_conway", ["fast/examples/conway.json", "--pointed",
                                            "--no-alexander", "--no-jones"], 0, "KNOTTED")

    def pointed_schema():
        result = pointed["result"]
        require("pointed" in result["method"], "pointed method not reported")
        decision = result["evidence"]["pointed_khovanov"]
        require(decision["status"] == "KNOTTED", "pointed decision disagrees with outer verdict")
        require(decision["lower_bound"] >= 2, "pointed knottedness has no sufficient rank bound")
        require("alexander_modular" not in result["evidence"], "disabled Alexander stage ran")
        require("jones" not in result["evidence"], "disabled Jones stage ran")

    add_check(pointed, "pointed decision route", pointed_schema)

    invalid = cli("invalid_pointed_race", ["fast/examples/conway.json", "--pointed", "--race", "2"], 2)
    add_check(invalid, "clean invalid-options error", lambda: require(
        "invalid options:" in invalid["stderr"] and not invalid["stdout"].strip(),
        "incompatible options must give one clean stderr error"))

    limited = cli("zero_budget_trefoil", ["fast/examples/trefoil.json", "--seconds", "0",
                                          "--no-reduction", "--no-descending"], 3, "UNKNOWN")
    add_check(limited, "resource-limit result", lambda: require(
        limited["result"]["method"] == "resource-limit"
        and "time budget exhausted" in limited["result"]["evidence"]["reason"],
        "zero budget did not produce the resource-limit schema"))

    # Exercise the public Python API from this same packaged version.
    sys.path.insert(0, str(ROOT / "fast"))
    import fastunknot
    from fastunknot.simplify import simplify

    api = {"name": "disabled_exact_alexander_api", "kind": "python_api",
           "call": "recognize(trefoil, use_modular=False, use_exact_alexander=False, use_jones=False)",
           "checks": [], "failures": []}
    cases.append(api)

    def api_disabled_stage():
        diagram = fastunknot.Diagram.from_json(json.loads(
            (ROOT / "fast" / "examples" / "trefoil.json").read_text()))
        result = fastunknot.recognize(diagram, use_modular=False,
                                     use_exact_alexander=False, use_jones=False).to_json()
        api["result"] = result
        api["status"] = result["status"]
        require(result["status"] == "KNOTTED", "disabled-stage options altered the knot verdict")
        message = result["evidence"]["alexander_polynomial"]
        require("disabled" in message and "unit" not in message,
                "evidence claims a modular calculation that did not run")
        require("alexander_modular" not in result["evidence"], "disabled modular stage produced evidence")

    add_check(api, "truthful disabled-stage evidence", api_disabled_stage)
    print(api["name"], "status", api.get("status", "error"), flush=True)

    def public_certificate_api():
        diagram = fastunknot.Diagram.from_json(json.loads(
            (ROOT / "fast" / "examples" / "conway_sum_2.json").read_text()))
        diagram, _ = simplify(diagram, r3=False)
        certificate = current["result"]["evidence"]["connected_sum_factorization"]
        require(fastunknot.verify_interlacement_certificate(
            [dart // 4 for dart in diagram.traversal()], certificate),
            "public verifier rejected CLI certificate")

    add_check(current, "public certificate verifier accepts CLI output", public_certificate_api)

    version = {"name": "package_version", "kind": "python_api",
               "call": "fastunknot.__version__", "version": fastunknot.__version__,
               "checks": [], "failures": []}
    cases.append(version)
    add_check(version, "version 0.3.0", lambda: require(
        fastunknot.__version__ == "0.3.0", "unexpected package version"))

    def packaging_metadata():
        # Read these two simple fields without requiring tomllib (the package
        # supports Python 3.10 as well as newer standard-library versions).
        text = (ROOT / "fast" / "pyproject.toml").read_text()
        project = text.split("[project]", 1)[1].split("\n[", 1)[0]
        declared_version = re.search(r'(?m)^version\s*=\s*"([^"]+)"', project).group(1)
        declared_license = re.search(r'(?m)^license\s*=\s*\{text\s*=\s*"([^"]+)"\}',
                                     project).group(1)
        version["pyproject_version"] = declared_version
        version["pyproject_license"] = declared_license
        require(declared_version == fastunknot.__version__, "packaging/runtime versions disagree")
        require(declared_license == "MIT-0", "unexpected packaging license")
        require("MIT No Attribution" in (ROOT / "LICENSE").read_text(),
                "root license text does not identify MIT No Attribution")

    add_check(version, "packaging version and MIT-0 metadata", packaging_metadata)

    for record in cases:
        record["passed"] = not record["failures"]
    source_hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in sorted((ROOT / "fast" / "fastunknot").glob("*.py"))}
    for relative in ("fast/pyproject.toml", "LICENSE"):
        source_hashes[relative] = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
    report = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(), "executable": sys.executable,
        "platform": platform.platform(), "package_version": fastunknot.__version__,
        "scope": "Six fresh-process CLI cases and two public-API checks; no full-suite rerun.",
        "passed": all(record["passed"] for record in cases),
        "cases": cases, "source_sha256": source_hashes,
    }
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print("Saved", output, flush=True)
    if not report["passed"]:
        for record in cases:
            for failure in record["failures"]:
                print(record["name"] + ": " + failure, file=sys.stderr)
        return 1
    print("All CLI/API integration checks passed.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
