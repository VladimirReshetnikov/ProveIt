#!/usr/bin/env python3
"""Verify and reproduce the finite artifacts shipped with the research report.

Python 3.12 was used for the recorded run. No third-party Python package,
network connection, Lean or Rocq installation is required. These finite
checks do not establish the outstanding ZFC/calculus/TM equivalence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
TABLES = {
    "raw-candidate-old_rho6-248.tm": (
        248, "e9cf9241e0012c56ecf4dc55f969d4c01e988a5c3839c9e4a49b5fae33591d45"),
    "raw-candidate-dual_rho6-248.tm": (
        248, "70d141e1a2872a3080b525a4061b48882131e636c41444f09bc065647a7e4a6c"),
    "benchmark-zfc-253.tm": (
        253, "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95"),
}


def require(condition: bool, explanation: str) -> None:
    if not condition:
        raise ValueError(explanation)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check() -> int:
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    files = manifest["files"]
    for name, entry in files.items():
        path = (ROOT / name).resolve()
        require(ROOT in path.parents, "manifest path escapes archive root")
        require(path.is_file(), "missing manifest file: " + name)
        require(path.stat().st_size == entry["bytes"], "size differs: " + name)
        require(sha256(path) == entry["sha256"], "hash differs: " + name)
    return len(files)


def table_check(name: str, n: int, expected: str) -> dict:
    path = ROOT / "machines" / name
    require(sha256(path) == expected, "unexpected table digest: " + name)
    rows = {}
    start = None
    for number, line in enumerate(path.read_text().splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if line.startswith("#! start "):
            require(start is None, "duplicate start declaration")
            start = int(line.split()[-1])
            continue
        if line.startswith("#"):
            continue
        parts = line.split()
        require(len(parts) == 5, f"bad row {number}: {name}")
        q, read, write, move, target = parts
        q, read, write, target = map(int, (q, read, write, target))
        require(0 <= q < n and 0 <= target <= n, "out-of-range state")
        require(read in (0, 1) and write in (0, 1), "nonbinary symbol")
        require(move in ("L", "R"), "unsupported tape move")
        require((q, read) not in rows, "duplicate state/symbol transition")
        rows[q, read] = (write, move, target)
    require(start == 0, "unexpected initial state")
    require(set(rows) == {(q, bit) for q in range(n) for bit in (0, 1)},
            "transition table is not total on working states")
    require(any(target == n for _, _, target in rows.values()), "no terminal edge")
    reached, pending = set(), [start]
    while pending:
        q = pending.pop()
        if q in reached or q == n:
            continue
        reached.add(q)
        pending.extend(rows[q, bit][2] for bit in (0, 1))
    require(len(reached) == n, "unexpected graph-unreachable state")
    return {"working_states": n, "transition_rows": len(rows), "start": start,
            "terminal_target": n, "graph_reachable_states": len(reached),
            "sha256": expected, "blank_symbol": 0, "tape": "two-way infinite"}


def run_json(args: list[str], cwd: Path | None = None) -> dict:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("PYTHONOPTIMIZE", None)
    completed = subprocess.run([sys.executable, "-B", *map(str, args)],
                               cwd=cwd, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if completed.returncode:
        raise RuntimeError(f"Check failed: {args[0]}\n{completed.stderr[-5000:]}")
    return json.loads(completed.stdout)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-regeneration", action="store_true",
                        help="check supplied tables/certificates without rebuilding tables")
    parser.add_argument("--output", type=Path,
                        help="optional JSON result path outside the extracted archive")
    args = parser.parse_args()
    require(not sys.flags.optimize, "Run without -O; upstream checkers use assertions")
    if args.output:
        destination = args.output.resolve()
        require(ROOT not in destination.parents and destination != ROOT,
                "write results outside the immutable archive")
    manifest_files = manifest_check()
    result = {"all_checks_passed": False,
              "manifest_files_checked": manifest_files,
              "python": sys.version.split()[0],
              "formal_kernel_verification": False,
              "new_machine_to_Con_ZFC_theorem_proved": False,
              "table_structure": {name: table_check(name, *info)
                                  for name, info in TABLES.items()}}
    with tempfile.TemporaryDirectory(prefix="zfc_candidate_reproduce_") as directory:
        work = Path(directory)
        codec = work / "codec_and_macros.py"
        shutil.copyfile(ROOT / "code" / codec.name, codec)
        checked_codec = run_json([str(codec)], cwd=work)
        expected_codec = json.loads((ROOT / "results" / "codec-and-macro-results.json").read_text())
        require(checked_codec == expected_codec, "codec/macro results differ from recorded run")
        result["codec_and_macro_checks"] = {
            "exact_codec_cases": checked_codec["codec"]["total"],
            "exact_macro_contracts": checked_codec["macros"]["total"],
            "AX_profiles": len(checked_codec["macros"]["profiles"]),
            "probabilistic_equality": False,
            "separating_models": checked_codec["relative_falsity_separating_model"]}
        psc = work / "psc_reference_checker"
        shutil.copytree(ROOT / "vendor" / "psc_reference_checker", psc)
        psc_output = work / "psc-validation.json"
        run_json([str(psc / "validate.py"), "--output", str(psc_output),
                  "--upstream-kernel",
                  str(ROOT / "vendor" / "ProveIt" / "Computability" /
                      "BusyBeaver" / "Research" / "ZFC" / "kernel_metrics.py")], cwd=psc)
        psc_check = json.loads(psc_output.read_text())
        require(psc_check["tests_successful"] and psc_check["tests_run"] == 12,
                "PSC reference tests failed")
        require(psc_check["upstream_comparison"]["sample_count"] == 6,
                "unexpected PSC comparison coverage")
        result["prior_PSC_reference_checker"] = {
            key: psc_check[key] for key in ("tests_run", "tests_successful",
                "deep_binder_test_depth", "substitution_semantics_comparisons",
                "identity", "bounded_census", "upstream_comparison")}
        result["independent_RM_certificates"] = {}
        prior = ROOT / "vendor" / "one_schema_machine"
        for variant in ("old_rho6", "dual_rho6"):
            verified = run_json([
                str(ROOT / "code" / "verify_schema_rm_certificate.py"),
                "--prior-machine-dir", str(prior),
                "--reference", str(ROOT / "machines" / f"{variant}-reference-dag.json"),
                "--candidate", str(ROOT / "machines" / f"{variant}-dag.json"),
                "--certificate", str(ROOT / "machines" / f"{variant}-rm-bisimulation.json")])
            require(verified["verified"] and verified["related_pairs"] == 3394,
                    "unexpected certificate result")
            result["independent_RM_certificates"][variant] = verified
        result["fixed_recipe_regenerated"] = not args.skip_regeneration
        if not args.skip_regeneration:
            generated = work / "generated"
            metadata = run_json([
                str(ROOT / "code" / "generate_schema_candidates.py"),
                "--repo", str(ROOT / "vendor" / "ProveIt"),
                "--rebracket-dir", str(prior), "--output", str(generated)])
            names = [name for name in TABLES if name.startswith("raw-candidate-")]
            for variant in ("old_rho6", "dual_rho6"):
                names += [f"{variant}-{suffix}" for suffix in (
                    "named.tm", "labels.json", "reference-dag.json", "dag.json",
                    "rm-bisimulation.json")]
            for name in names:
                require((generated / name).read_bytes() == (ROOT / "machines" / name).read_bytes(),
                        "fixed recipe did not reproduce " + name)
            result["regenerated_files_matching_byte_for_byte"] = names
            result["generator_source_sha256"] = metadata["generator_sha256"]
    result["all_checks_passed"] = True
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
