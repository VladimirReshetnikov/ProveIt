#!/usr/bin/env python3
"""Run the retained tests and independent saved-certificate replays.

The three research layers run in separate processes with their bundled import
paths. No benchmark, Regina oracle, full vertex census, or PDF build is run.
Results and full per-group logs are written under results/ by default.
"""
from __future__ import annotations

import argparse
from contextlib import ExitStack
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parent
GROUPS = {
    "routing_tests": {"kind": "tests", "cwd": ".", "paths": ["code"]},
    "geometry_tests": {"kind": "tests", "cwd": "geometry",
                       "paths": ["geometry/code", "geometry/vendor"]},
    "cancellation_tests": {"kind": "tests", "cwd": "cancellation",
                           "paths": ["cancellation"]},
    "routing_replays": {"kind": "replays", "cwd": ".", "paths": ["code"]},
    "geometry_replays": {"kind": "replays", "cwd": "geometry",
                         "paths": ["geometry/code", "geometry/vendor"]},
    "cancellation_replay": {"kind": "replays", "cwd": "cancellation",
                            "paths": ["cancellation"]},
}
GRAPH_EXAMPLES = (
    "routed_4097_bits", "mixed_1025_bits", "positive_tetrahedron",
    "through_4097_bits",
)
GEOMETRY_EXAMPLES = (
    "pilot_lst_5_7_0_certificate.json",
    "pilot_pachner23_3_5_1_0_certificate.json",
    "pilot_pachner23_5_8_1_0_certificate.json",
    "pilot_pachner23_5_8_2_0_certificate.json",
    "lst_3_8_mixed_certificate.json",
)


def relative(path):
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return str(Path(path).resolve())


def file_record(path):
    data = Path(path).read_bytes()
    return {"path": relative(path), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def write_json(path, record):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")


def pinned_dependencies():
    """Check byte-for-byte provenance without importing a research module."""
    records = []
    geometrical = json.loads((ROOT / "geometry/evidence/upstream_dependencies.json").read_text())
    cancellation = json.loads((ROOT / "provenance/cancellation_dependencies.json").read_text())
    requested = []
    for item in geometrical["files"]:
        requested.append((ROOT / "geometry/vendor" / item["path"], item, "geometry_module"))
    for item in geometrical["extra_files"]:
        requested.append((ROOT / "geometry/vendor" / item["path"], item, "geometry_fixture"))
    for item in cancellation["modules"]:
        module_path = Path(*item["module"].split(".")).with_suffix(".py")
        requested.append((ROOT / "cancellation/runtime/fast" / module_path,
                          item, "cancellation_module"))
    for path, expected, kind in requested:
        record = {"path": relative(path), "kind": kind,
                  "expected_sha256": expected["sha256"]}
        try:
            record.update(file_record(path))
            record["passed"] = (record["sha256"] == expected["sha256"]
                                and record["bytes"] == expected["bytes"])
        except OSError as exc:
            record.update(passed=False, error=str(exc))
        records.append(record)
    fixture = ROOT / "cancellation/runtime" / cancellation["fixture"]
    # The cancellation manifest names this fixture but does not supply its hash.
    # Record the actual bytes; do not invent a historical hash comparison.
    fixture_record = file_record(fixture)
    return {
        "passed": all(item["passed"] for item in records),
        "module_files_checked": sum(item["kind"].endswith("module") for item in records),
        "fixture_files_hash_checked": sum(item["kind"].endswith("fixture") for item in records),
        "files": records,
        "cancellation_fixture_present": fixture_record,
        "namespace_shims": "Generated minimal __init__.py files are not upstream module copies.",
    }


def disabled_producers(names):
    """Any accidental call back into a listed producer fails the replay."""
    stack = ExitStack()
    try:
        for name in names:
            stack.enter_context(patch(name, side_effect=AssertionError(
                "saved-certificate replay called producer " + name)))
    except BaseException:
        stack.close()
        raise
    return stack


def run_tests():
    suite = unittest.defaultTestLoader.discover("tests", pattern="test*.py")
    discovered = suite.countTestCases()
    result = unittest.TextTestRunner(stream=sys.stdout, verbosity=2).run(suite)
    record = {
        "kind": "tests", "tests_discovered": discovered,
        "tests_run": result.testsRun, "failures": len(result.failures),
        "errors": len(result.errors), "skipped": len(result.skipped),
        "expected_failures": len(result.expectedFailures),
        "unexpected_successes": len(result.unexpectedSuccesses),
        "skipped_tests": [{"id": test.id(), "reason": reason}
                          for test, reason in result.skipped],
    }
    # The bundled validation is complete only if all discovered methods ran.
    # An optional-native-runtime skip must never look like a full package pass.
    record["passed"] = (discovered > 0 and result.testsRun == discovered
                        and result.wasSuccessful() and not result.skipped
                        and not result.expectedFailures)
    return record


def routing_replays():
    from routed_patterns.core import parse_chain
    from routed_patterns.verify import verify_result as aligned_verify
    from routed_patterns.verify import verify_source_witness as aligned_source
    from routed_patterns.stable_verify import verify_result as through_verify
    from routed_patterns.stable_verify import verify_source_witness as through_source

    blocked = [
        "routed_patterns.core.solve", "routed_patterns.core.build_kernel",
        "routed_patterns.core.plan_block", "routed_patterns.core.source_witness",
        "routed_patterns.core.components", "routed_patterns.core.certify_cubic_graph",
        "routed_patterns.stable.solve", "routed_patterns.stable.reblock_chain",
        "routed_patterns.stable.build_kernel", "routed_patterns.stable.through_components",
        "routed_patterns.stable.aligned_solve", "routed_patterns.stable.aligned_build_kernel",
        "routed_patterns.stable.aligned_components", "pattern_kernel.core.certify_cubic_graph",
        "pattern_kernel.core._flow", "pattern_kernel.core.solve",
        "pattern_kernel.core.kernelize", "pattern_kernel.core.expand",
        "pattern_kernel.core.lift_witness",
    ]
    required = {ROOT / "examples" / (name + "_certificate.json") for name in GRAPH_EXAMPLES}
    files = sorted(required | set((ROOT / "examples").glob("*_certificate.json")))
    records = []
    with disabled_producers(blocked):
        for path in files:
            record = {"certificate_path": relative(path), "passed": False}
            try:
                source_path = path.with_name(path.name.removesuffix("_certificate.json") + ".json")
                payload = json.loads(source_path.read_text())
                proof = json.loads(path.read_text())
                chain = parse_chain(payload)
                schema = proof.get("schema")
                if schema == "routed-cubic-cut-v1":
                    accepted = aligned_verify(chain, proof)
                    verdict = proof["graph_proof"]["verdict"]
                    source = (aligned_source(chain, proof["source_witness"])
                              if accepted and verdict == "LOW_CYCLIC_CUT" else None)
                elif schema == "stable-routed-cubic-cut-v1":
                    accepted = through_verify(chain, proof)
                    verdict = proof["verdict"]
                    source = (through_source(chain, proof)
                              if accepted and verdict == "LOW_CYCLIC_CUT" else None)
                else:
                    raise ValueError("unsupported graph certificate schema: " + str(schema))
                record.update(source_file=file_record(source_path), certificate_file=file_record(path),
                              schema=schema, verdict=verdict, passed=bool(accepted))
                if source is not None:
                    record["original_source_witness"] = source
            except Exception:
                record["error"] = traceback.format_exc()
            print(json.dumps({"path": record["certificate_path"], "accepted": record["passed"]}), flush=True)
            if "error" in record:
                print(record["error"], flush=True)
            records.append(record)
    return replay_report(records, blocked)


def geometry_replays():
    from unsaturated_bundles.native import verify_normal_cut_unsaturated_handlebodies
    from unsaturated_bundles.finite import decode

    blocked = [
        "unsaturated_bundles.native.normal_cut_unsaturated_handlebodies",
        "unsaturated_bundles.native.make_certificate",
        "unsaturated_bundles.finite.make_certificate",
        "fastunknot.normal_parallelity.normal_cut_parallelity",
        "fastunknot.core_handlebody.core_handlebody_certificate",
        "fastunknot.parallelity_boundary_words.normal_parallelity_boundary_words",
        "fastunknot.normal_cut_handlebodies.normal_cut_handlebodies",
    ]
    directory = ROOT / "geometry/evidence"
    files = sorted({directory / name for name in GEOMETRY_EXAMPLES}
                   | set(directory.glob("*_certificate.json")))
    records = []
    with disabled_producers(blocked):
        for path in files:
            record = {"certificate_path": relative(path), "passed": False}
            try:
                saved = json.loads(path.read_text())
                source, proof = saved["source"], saved["certificate"]
                accepted = verify_normal_cut_unsaturated_handlebodies(
                    source["triangulation"], source["coordinates"], proof)
                record.update(file=file_record(path), schema=proof.get("schema"), passed=bool(accepted))
                if accepted:
                    record["verified_census"] = decode(proof["reduction"]["census"])
            except Exception:
                record["error"] = traceback.format_exc()
            print(json.dumps({"path": record["certificate_path"], "accepted": record["passed"]}), flush=True)
            if "error" in record:
                print(record["error"], flush=True)
            records.append(record)
    return replay_report(records, blocked)


def cancellation_replay():
    import bootstrap  # Uses the worker's explicitly selected bundled runtime.
    from fastunknot.normal_vertex_gate import verify_vertex_disc_certificate

    blocked = [
        "fastunknot.normal_vertex_gate.produce_vertex_disc_certificate",
        "fastunknot.normal_vertex_gate._find_rank_minor",
        "fastunknot.normal_weight_clusters.cluster_defect_search",
        "fastunknot.normal_weight_clusters.enumerate_cluster_candidates",
    ]
    path = ROOT / "cancellation/artifacts/disconnected_disc.json"
    record = {"certificate_path": relative(path), "passed": False}
    with disabled_producers(blocked):
        try:
            saved = json.loads(path.read_text())
            proof = saved["certificate"]
            accepted = verify_vertex_disc_certificate(
                saved["triangulation"], saved["coordinates"], proof)
            record.update(file=file_record(path), schema=proof.get("schema"),
                          tetrahedra=len(saved["triangulation"]["tetrahedra"]),
                          passed=bool(accepted),
                          replay_scope="Supplied primitive essential disc; no negative census or search-completeness claim.")
        except Exception:
            record["error"] = traceback.format_exc()
    print(json.dumps({"path": record["certificate_path"], "accepted": record["passed"]}), flush=True)
    if "error" in record:
        print(record["error"], flush=True)
    return replay_report([record], blocked)


def replay_report(records, blocked):
    return {
        "kind": "replays", "certificates_checked": len(records),
        "certificates_accepted": sum(record["passed"] for record in records),
        "producer_entrypoints_disabled": blocked, "cases": records,
        "passed": bool(records) and all(record["passed"] for record in records),
    }


def worker(group, result_path):
    config = GROUPS[group]
    os.chdir(ROOT / config["cwd"])
    sys.path[:0] = [str(ROOT / path) for path in config["paths"]]
    started = time.perf_counter()
    try:
        if config["kind"] == "tests":
            result = run_tests()
        else:
            result = globals()[group]()
    except Exception:
        result = {"kind": config["kind"], "passed": False, "error": traceback.format_exc()}
        print(result["error"], flush=True)
    result.update(group=group, elapsed_seconds=time.perf_counter() - started)
    write_json(result_path, result)
    return 0 if result["passed"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", choices=("all", "tests", "replays"), default="all")
    parser.add_argument("--output", type=Path, default=ROOT / "results/verify_all.json")
    parser.add_argument("--log-dir", type=Path, default=ROOT / "results/verification")
    parser.add_argument("--timeout", type=float, default=600,
                        help="maximum seconds per isolated group (default: 600)")
    parser.add_argument("--_worker", choices=tuple(GROUPS), help=argparse.SUPPRESS)
    parser.add_argument("--_result", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args._worker:
        if args._result is None:
            parser.error("internal worker requires a result path")
        return worker(args._worker, args._result)
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    output, log_dir = args.output.resolve(), args.log_dir.resolve()
    log_dir.mkdir(parents=True, exist_ok=True)
    selected = [name for name, config in GROUPS.items()
                if args.only == "all" or config["kind"] == args.only]
    report = {
        "schema": "unknot-hierarchy-kernels-validation-v1",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(), "platform": platform.platform(),
        "runner": file_record(Path(__file__)), "selected_groups": selected,
        "scope": "Retained unit tests and producer-disabled saved-certificate replays. No benchmarks, external oracle census, diagram recognition, or PDF build.",
        "groups": [], "status": "RUNNING", "all_passed": False,
    }
    try:
        report["pinned_dependencies"] = pinned_dependencies()
    except Exception:
        report["pinned_dependencies"] = {"passed": False, "error": traceback.format_exc()}
    write_json(output, report)
    if not report["pinned_dependencies"]["passed"]:
        report.update(status="FAILED_PREFLIGHT", finished_utc=datetime.now(timezone.utc).isoformat())
        write_json(output, report)
        print("Pinned dependency preflight failed; see " + str(output), flush=True)
        return 1
    print("Pinned dependency hashes accepted.", flush=True)
    for group in selected:
        config = GROUPS[group]
        result_path, log_path = log_dir / (group + ".json"), log_dir / (group + ".log")
        if result_path.exists():
            result_path.unlink()  # A stale worker result cannot mask a failed rerun.
        env = os.environ.copy()
        env.update(PYTHONPATH=os.pathsep.join(str(ROOT / p) for p in config["paths"]),
                   PYTHONNOUSERSITE="1", PYTHONDONTWRITEBYTECODE="1", PYTHONUNBUFFERED="1",
                   PYTHONHASHSEED="0", PROVEIT_UNKNOT_ROOT=str(ROOT / "cancellation/runtime"),
                   CANCELLATION_PACKAGE=str(ROOT / "cancellation/runtime"))
        command = [sys.executable, str(Path(__file__).resolve()), "--_worker", group,
                   "--_result", str(result_path)]
        print("Running " + group + " ...", flush=True)
        started = time.perf_counter()
        exit_code, execution_error = None, None
        try:
            with log_path.open("w", encoding="utf-8") as log:
                completed = subprocess.run(command, cwd=ROOT / config["cwd"], env=env,
                                           stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
                exit_code = completed.returncode
        except (OSError, subprocess.TimeoutExpired) as exc:
            execution_error = str(exc)
        try:
            result = json.loads(result_path.read_text())
        except (OSError, ValueError):
            result = {"group": group, "kind": config["kind"], "passed": False,
                      "error": "Worker did not write a readable result."}
        result.update(exit_code=exit_code, log=relative(log_path), result_file=relative(result_path),
                      cwd=config["cwd"], pythonpath=config["paths"],
                      process_elapsed_seconds=time.perf_counter() - started)
        if exit_code != 0:
            result["passed"] = False
        if execution_error:
            result["execution_error"] = execution_error
        report["groups"].append(result)
        write_json(output, report)
        noun, count = (("test methods", result.get("tests_run", 0)) if config["kind"] == "tests"
                       else ("saved certificates", result.get("certificates_checked", 0)))
        print(("PASS " if result["passed"] else "FAIL ") + group + ": " + str(count) + " " + noun,
              flush=True)
    report["counts"] = {
        "groups": len(report["groups"]),
        "groups_passed": sum(item["passed"] for item in report["groups"]),
        "test_methods_run": sum(item.get("tests_run", 0) for item in report["groups"]),
        "test_failures": sum(item.get("failures", 0) for item in report["groups"]),
        "test_errors": sum(item.get("errors", 0) for item in report["groups"]),
        "test_skips": sum(item.get("skipped", 0) for item in report["groups"]),
        "saved_certificates_checked": sum(item.get("certificates_checked", 0) for item in report["groups"]),
        "saved_certificates_accepted": sum(item.get("certificates_accepted", 0) for item in report["groups"]),
    }
    passed = len(report["groups"]) == len(selected) and all(item["passed"] for item in report["groups"])
    report.update(status="PASSED" if passed else "FAILED", all_passed=passed,
                  finished_utc=datetime.now(timezone.utc).isoformat())
    write_json(output, report)
    print(json.dumps({"status": report["status"], "counts": report["counts"],
                      "summary": relative(output)}, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
