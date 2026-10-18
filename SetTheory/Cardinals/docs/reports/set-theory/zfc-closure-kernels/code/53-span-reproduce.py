#!/usr/bin/env python3
"""Reproduce the finite evidence in the permutation252 reduction study.

Python 3.10+ and, for searches/variant, g++ with C++17 are sufficient.
The package is read-only input. Every rerun writes below a separate --out.
No command installs software, uses the network, or invokes Lean/Coq.
"""
from __future__ import annotations

import argparse
from collections import deque
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time


PACKAGE = Path(__file__).resolve().parent
ZFC = Path("Computability/BusyBeaver/Research/ZFC")
VARIANT_LEDGER_SHA256 = "6f0c9975f067af006280482b4c38df628f7e240b7b8dcbb0bb5a4ce30e9ccb3e"


class ReproductionError(RuntimeError):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ReproductionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def without_fields(value, excluded: set[str]):
    if isinstance(value, dict):
        return {k: without_fields(v, excluded) for k, v in value.items() if k not in excluded}
    if isinstance(value, list):
        return [without_fields(v, excluded) for v in value]
    return value


def verify_package(args) -> None:
    manifest = args.manifest
    if manifest is None:
        manifest = next((PACKAGE / name for name in ("SHA256SUMS.txt", "SHA256SUMS")
                         if (PACKAGE / name).is_file()), None)
    else:
        manifest = manifest.resolve()
    need(manifest is not None, "No SHA256SUMS.txt or SHA256SUMS file is present.")
    seen = set()
    for number, line in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64}) [ *](.+)", line)
        need(match is not None, f"Unsupported checksum line {number} in {manifest}.")
        expected, name = match.groups()
        relative = Path(name)
        need(not relative.is_absolute() and ".." not in relative.parts,
             f"Checksum path must remain inside the package: {name}")
        path = (PACKAGE / relative).resolve()
        need(PACKAGE in path.parents, f"Checksum path leaves the package: {name}")
        need(name not in seen, f"Duplicate checksum entry: {name}")
        need(path.is_file(), f"Missing checksum input: {name}")
        need(sha256(path) == expected.lower(), f"SHA-256 mismatch: {name}")
        seen.add(name)
    need(bool(seen), "The checksum manifest contains no file entries.")
    print(f"PASS: all {len(seen)} listed file hashes match {manifest.name}.")
    print("This verifies file integrity; it does not rerun a proof or experiment.")


class Run:
    def __init__(self, args):
        self.args = args
        self.dry = args.dry_run
        self.root = args.out.expanduser().resolve()
        need(self.root != PACKAGE and PACKAGE not in self.root.parents,
             "--out must be outside the delivered package.")
        self.work = (self.root / args.command).resolve()
        need(self.work != PACKAGE and PACKAGE not in self.work.parents,
             "The command output directory must be outside the package.")
        if self.work.exists():
            need(self.work.is_dir() and not any(self.work.iterdir()),
                 f"Output directory is not empty: {self.work}. Choose another --out.")
        self.repo = PACKAGE / "upstream"
        need(self.repo.is_dir(), f"Missing vendored upstream subset: {self.repo}")
        self.commands = []
        self.checks = []
        if not self.dry:
            (self.work / "logs").mkdir(parents=True)

    def run(self, label: str, argv, cwd: Path | None = None) -> None:
        argv = [str(x) for x in argv]
        cwd = cwd or self.work
        print(f"[{label}] {shlex.join(argv)}", flush=True)
        if self.dry:
            self.commands.append({"label": label, "argv": argv, "cwd": str(cwd)})
            return
        log = self.work / "logs" / (label + ".log")
        started = time.monotonic()
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env.pop("PYTHONOPTIMIZE", None)
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(argv, cwd=cwd, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        self.commands.append({"label": label, "argv": argv, "cwd": str(cwd),
                              "log": str(log.relative_to(self.work)),
                              "returncode": result.returncode,
                              "elapsed_seconds": time.monotonic() - started})
        if result.returncode:
            with log.open(encoding="utf-8", errors="replace") as stream:
                tail = "".join(deque(stream, maxlen=35))
            raise ReproductionError(f"{label} failed with exit {result.returncode}.\n{tail}\nLog: {log}")
        print(f"  completed; log: {log}", flush=True)

    def python(self, label: str, script: Path, *args, cwd: Path | None = None) -> None:
        self.run(label, [sys.executable, "-B", script, *args], cwd)

    def compile(self, source: str) -> Path:
        target = self.work / "bin" / Path(source).stem
        if not self.dry:
            target.parent.mkdir(exist_ok=True)
        self.run("compile-" + target.name,
                 [self.args.cxx, "-O3", "-std=c++17", PACKAGE / "machine_search" / source,
                  "-o", target])
        return target

    def copy(self, name: str) -> Path:
        source, destination = PACKAGE / name, self.work / name
        need(source.is_dir(), f"Missing input directory: {source}")
        print(f"[copy] {source} -> {destination}", flush=True)
        if not self.dry:
            shutil.copytree(source, destination,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        return destination

    def decompress(self, source: Path, target: Path) -> None:
        need(source.is_file(), f"Missing compressed input: {source}")
        print(f"[decompress] {source} -> {target}", flush=True)
        if not self.dry:
            target.parent.mkdir(parents=True, exist_ok=True)
            with gzip.open(source, "rb") as stream, target.open("wb") as output:
                shutil.copyfileobj(stream, output)

    def digest(self, actual: Path, expected: str, label: str) -> None:
        if self.dry:
            return
        found = sha256(actual)
        need(found == expected, f"{label}: SHA-256 mismatch ({found}, expected {expected}).")
        self.checks.append({"check": label, "sha256": found, "status": "PASS"})

    def same_file(self, actual: Path, expected: Path) -> None:
        need(expected.is_file(), f"Missing reference file: {expected}")
        if not self.dry:
            self.digest(actual, sha256(expected), str(expected.relative_to(PACKAGE)))

    def same_json(self, actual: Path, expected: Path, excluded=()) -> None:
        need(expected.is_file(), f"Missing reference JSON: {expected}")
        if self.dry:
            return
        left, right = read_json(actual), read_json(expected)
        need(without_fields(left, set(excluded)) == without_fields(right, set(excluded)),
             f"JSON content differs from {expected}; comparison ignores only {sorted(excluded)}.")
        self.checks.append({"check": str(expected.relative_to(PACKAGE)), "status": "PASS",
                            "excluded_metadata_fields": sorted(excluded)})

    def finish(self) -> None:
        if self.dry:
            print("Dry run complete: no output directories, compilers, or experiments were run.")
            return
        record = {"status": "PASS", "command": self.args.command,
                  "package": str(PACKAGE), "upstream_subset": str(self.repo),
                  "python": sys.version, "commands": self.commands, "checks": self.checks,
                  "scope": "Reproduction of finite evidence only; no new consistency or state lower-bound theorem."}
        target = self.work / "reproduction.json"
        target.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        print(f"PASS: {self.args.command}; reproduction record: {target}")


def baseline(run: Run) -> None:
    target = run.work / "baseline-audit.json"
    run.python("baseline-audit", run.repo / ZFC / "candidate252_independent_audit.py",
               "--repo", run.repo,
               "--source-table", run.repo / ZFC / "candidate-permutation252/zfc_permutation252_old.tm",
               "--scratch", run.work / "scratch", "--output", target)
    if not run.dry:
        result = read_json(target)
        need(result["status"] == "all_finite_checks_passed", "Baseline audit did not pass.")
        need((result["working_states"], result["total_rows"], result["literal_boot_steps"],
              result["affine_audit"]["passed_cases"]) == (252, 504, 82552, 8391),
             "Unexpected baseline state, row, bootstrap, or guard count.")
        run.checks.append({"check": "baseline finite audit", "status": "PASS",
                           "working_states": 252, "rows": 504, "blank_steps": 82552,
                           "affine_cases": 8391})


def compare_preparation(run: Run, destination: Path, reference: str) -> None:
    for name in ("baseline.tm", "cases.tsv", "family.tsv", "preparation.json"):
        run.same_file(destination / name, PACKAGE / "machine_search" / reference / name)


def completed_frontier(run: Run, prefix: Path) -> None:
    if not run.dry:
        need(Path(str(prefix) + ".frontier.tsv").stat().st_size == 0,
             f"Search stopped with a nonempty frontier: {prefix}. Increase --seconds and use a fresh --out; this is not a completed reproduction.")


def searches(run: Run) -> None:
    machine = PACKAGE / "machine_search"
    data = run.work / "action_data"
    run.python("prepare-actions", machine / "prepare_actions.py",
               "--repo", run.repo, "--out", data)
    compare_preparation(run, data, "action_data")
    families = set(run.args.families)
    executable = run.compile("action_search.cpp") if families & {"target2", "action2"} else None
    for family, prefix_name, target_only, choices in (
            ("target2", "target_control", 1, 251),
            ("action2", "all_actions", 0, 1008)):
        if family not in families:
            continue
        prefix = run.work / prefix_name
        run.run(family, [executable, data, prefix, run.args.seconds, 0, 46, target_only])
        completed_frontier(run, prefix)
        reference = machine / (prefix_name + ".audit.json")
        run.digest(Path(str(prefix) + ".ledger.tsv"), read_json(reference)["ledger_sha256"],
                   family + " deterministic ledger")
        audit_args = ["--ledger", Path(str(prefix) + ".ledger.tsv"), "--data", data,
                      "--actions", choices, "--output", Path(str(prefix) + ".audit.json")]
        if family == "target2":
            journal = run.work / "lazy-nodes.jsonl"
            run.decompress(PACKAGE / "analysis/lazy-nodes.jsonl.gz", journal)
            audit_args += ["--python-journal", journal]
        run.python("audit-" + family, machine / "audit_action_partition.py", *audit_args)
        run.same_json(Path(str(prefix) + ".audit.json"), reference)
        if family == "action2":
            replay = run.work / "action-failure-replay.json"
            run.python("replay-action-failures", PACKAGE / "analysis/replay_action_failures.py",
                       "--repo", run.repo, "--machine-work", run.work, "--output", replay)
            if not run.dry:
                result = read_json(replay)
                need(result.get("status") == "PASS" and result.get("sampled_failures") == 1472,
                     "Independent sampled action replay did not pass all 1,472 controls.")
                run.checks.append({"check": "fixed-seed independent Python failure replay",
                                   "status": "PASS", "scope": "1,472 sampled failures; not exhaustive replay"})
            run.same_json(replay, PACKAGE / "analysis/action-failure-replay.json")
    if "target3" in families:
        multidata = run.work / "multi_data"
        run.python("prepare-multi", machine / "prepare_multi.py",
                   "--repo", run.repo, "--data", data, "--out", multidata)
        compare_preparation(run, multidata, "multi_data")
        executable = run.compile("action_search_multi.cpp")
        prefix = run.work / "multi_target_degree3"
        run.run("target3", [executable, multidata, prefix, run.args.seconds, 3, 3, 1])
        completed_frontier(run, prefix)
        reference = machine / "multi_target_degree3.audit.json"
        run.digest(Path(str(prefix) + ".ledger.tsv"), read_json(reference)["ledger_sha256"],
                   "target3 deterministic ledger")
        result_path = Path(str(prefix) + ".audit.json")
        run.python("audit-target3", machine / "audit_multi_partition.py",
                   "--prefix", prefix, "--data", multidata, "--min-degree", 3,
                   "--max-degree", 3, "--actions", 251,
                   "--source", machine / "action_search_multi.cpp", "--output", result_path)
        run.same_json(result_path, reference, excluded={"elapsed_seconds"})


def codecs(run: Run) -> None:
    directory = run.copy("codecs")
    run.python("affine-codecs", directory / "affine_codec_search.py",
               "--max-modulus", 12, "--output", directory / "affine_codec_results.json", cwd=directory)
    run.python("constructor-map", directory / "map_constructor_subtrees.py", cwd=directory)
    run.python("optimized-tag-swap", directory / "swap_tags_optimized.py",
               "--repo", run.repo, "--factor", "direct",
               "--output", directory / "swap_tags_results.json", cwd=directory)
    run.python("dual-bottom-control", directory / "dual_bottom4_cost.py", cwd=directory)
    for name in ("affine_codec_results.json", "constructor_subtree_mapping.json",
                 "swap_tags_results.json", "swap_tags_optimized_nodes.json", "swap_tags_source_dag.json",
                 "swap_tags_segment_certificate.json", "swap_tags_guard_cases.json", "dual_bottom4_results.json"):
        run.same_json(directory / name, PACKAGE / "codecs" / name, excluded={"seconds", "elapsed_seconds"})
    for name in ("affine_codec_results.tm", "swap_tags_runtime.tm", "swap_tags_runtime_old.tm"):
        run.same_file(directory / name, PACKAGE / "codecs" / name)


def semantics(run: Run) -> None:
    directory = run.copy("semantics")
    run.python("mp-birth", directory / "mp_birth_cost.py", cwd=directory)
    run.python("deterministic-mp", directory / "deterministic_mp_cost.py", cwd=directory)
    for folder in ("mp_birth_results", "deterministic_mp_results"):
        reference = PACKAGE / "semantics" / folder
        # Input-path strings change when the original agent_proof directory is relocated.
        excluded = {"source_sha256"} if folder == "mp_birth_results" else set()
        run.same_json(directory / folder / "results.json", reference / "results.json",
                      excluded=excluded)
        if excluded and not run.dry:
            def relative_hashes(path):
                return {Path(*Path(name).parts[1:]).as_posix(): digest
                        for name, digest in read_json(path)["source_sha256"].items()}
            need(relative_hashes(directory / folder / "results.json") ==
                 relative_hashes(reference / "results.json"),
                 "Semantic source hashes differ after normalizing the relocated directory prefix.")
            run.checks.append({"check": "MP-birth input hashes after directory-prefix normalization",
                               "status": "PASS"})
        for original in sorted(reference.iterdir()):
            if original.suffix == ".tm" or original.name.endswith("-dag.json"):
                run.same_file(directory / folder / original.name, original)


def phase(run: Run) -> None:
    result = run.work / "modular-phase.json"
    run.python("modular-phase", PACKAGE / "analysis/modular_phase.py",
               "--repo", run.repo, "--output", result)
    run.same_json(result, PACKAGE / "analysis/modular-phase.json", excluded={"elapsed_seconds"})


def variant(run: Run) -> None:
    machine, data = PACKAGE / "machine_search", run.work / "variant_data"
    run.python("prepare-variant", machine / "prepare_variant.py", "--repo", run.repo,
               "--variant", PACKAGE / "codecs", "--out", data)
    for name in ("baseline.tm", "cases.tsv", "folds.tsv", "source_cases.json", "preparation.json"):
        run.same_file(data / name, machine / "variant_data" / name)
    executable = run.compile("variant_fold_search.cpp")
    prefix = run.work / "variant_folds"
    run.run("variant-folds", [executable, data, prefix])
    run.digest(Path(str(prefix) + ".ledger.tsv"), VARIANT_LEDGER_SHA256,
               "254-state tag-swap runtime uniform-fold ledger")
    run.same_json(Path(str(prefix) + ".summary.json"), machine / "variant_folds.summary.json",
                  excluded={"elapsed_seconds"})


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    verify = sub.add_parser("verify", help="Check every entry of the package SHA256SUMS manifest.")
    verify.add_argument("--manifest", type=Path, help="Checksum manifest; defaults to package SHA256SUMS.txt.")
    for name, description in (
            ("baseline", "Rebuild and fully audit the frozen 252-state finite candidate evidence."),
            ("searches", "Rerun completed target2, action2, and target3 searches and audit their ledgers."),
            ("codecs", "Rerun the complete affine census and optimized All/Eq tag-swap controls."),
            ("semantics", "Rerun the MP first-production and deterministic-MP compiler controls."),
            ("phase", "Recompute all 25 natural-value post-fixpoint certificates."),
            ("variant", "Audit 8,408 guards and all 56,419 uniform folds of the 254-state runtime.")):
        command = sub.add_parser(name, help=description)
        command.add_argument("--out", type=Path, required=True,
                             help="Output parent outside the package; its command-named subdirectory must be empty.")
        command.add_argument("--dry-run", action="store_true", help="Print commands without running them or creating output.")
        if name in ("searches", "variant"):
            command.add_argument("--cxx", default="g++", help="C++ compiler executable (default: g++).")
        if name == "searches":
            command.add_argument("--families", nargs="+", choices=("target2", "action2", "target3"),
                                 default=["target2", "action2", "target3"])
            command.add_argument("--seconds", type=float, default=600,
                                 help="Maximum elapsed seconds per search family; incomplete runs fail comparison.")
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions must remain enabled; do not invoke Python with -O or PYTHONOPTIMIZE.")
    try:
        if args.command == "verify":
            verify_package(args)
        else:
            if args.command == "searches":
                need(math.isfinite(args.seconds) and args.seconds > 0, "--seconds must be finite and positive.")
            run = Run(args)
            globals()[args.command](run)
            run.finish()
        return 0
    except (ReproductionError, OSError, ValueError, KeyError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
