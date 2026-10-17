#!/usr/bin/env python3
"""Reproduce the report's finite evidence offline, using only Python's stdlib.

Run from any working directory:
    python3 /path/to/archive/tools/reproduce.py --quick
    python3 /path/to/archive/tools/reproduce.py --full
    python3 /path/to/archive/tools/reproduce.py --searches

Each invocation creates a fresh directory under reproduced/.  The latest
verification_summary.json is also written directly in reproduced/.  Original
sources and evidence are read-only inputs.  Full mode adds the four-object
packing census; searches mode additionally replays both macro searches and
the complete bounded mixed-row search.  No proof-assistant build is claimed.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
TABLE_REL = "busy-beaver/ZF/m253/machine/zfc_253.tm"
BASELINE_REQUIRED = {
    "audit_tm.py", "mixed_merge_search.py", "summarize_mixed.py",
    "mixed_merge_results.json", "mixed_merge_summary.json",
    "public253_macro_r4.json", "public253_macro_r6.json",
    "helpers/context_search.py", "helpers/analyze_table.py", TABLE_REL,
    "busy-beaver/ZF/m253/tools/generate_candidate.py",
    "busy-beaver/ZF/m254/machine/zfc_254.tm",
    "busy-beaver/ZF/m254/coq/tm/Prog254.v",
    "busy-beaver/ZF/m254/tools/tm/symexec.py",
    "busy-beaver/ZF/generator/LICENSE.wade", "BASELINE_FINDINGS.md",
}

# Read the saved words back independently of their generation.  A theory
# preset is deliberately external to the word, as specified in the report.
CERTIFICATE_CHECK = r'''
import json
from pathlib import Path
import sys
sys.path.insert(0, sys.argv[1])
import closure_reference as closure
goal = ("ex", ("all", ("imp", ("mem", 0, 1), ("bot",))))
result = {}
for variant, original, regenerated in (
        ("epsc", sys.argv[2], sys.argv[3]),
        ("xfp", sys.argv[4], sys.argv[5])):
    old = Path(original).read_bytes()
    new = Path(regenerated).read_bytes()
    if old != new:
        raise SystemExit("Positive certificate bytes differ: " + variant)
    word = new.decode("ascii")
    certificate = closure.decode(word)
    if certificate is None:
        raise SystemExit("Saved certificate did not decode: " + variant)
    if not closure.check(*certificate, goal=goal, variant=variant,
                         fixed_axiom="adjunction"):
        raise SystemExit("Saved empty-object proof was rejected: " + variant)
    if closure.refutation_word(word, variant=variant, fixed_axiom="adjunction"):
        raise SystemExit("An empty-object proof was called a refutation.")
    result[variant] = {"bits": len(word), "nodes": len(certificate[1]),
                       "accepted": True, "is_refutation": False}
print(json.dumps(result, indent=2, sort_keys=True))
'''


class VerificationError(Exception):
    """A finite replay did not match its declared source or expected evidence."""


def read_json(path: Path):
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")


def relative_file(base: Path, name: str) -> Path:
    """Keep manifest paths inside their declared local source tree."""
    if not isinstance(name, str) or Path(name).is_absolute():
        raise VerificationError("Manifest path must be a relative string.")
    candidate = (base / name).resolve()
    if not candidate.is_relative_to(base.resolve()):
        raise VerificationError("Manifest path escapes its source tree: " + name)
    if not candidate.is_file():
        raise VerificationError("Required file is missing: " + str(candidate))
    return candidate


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def first_difference(expected, actual, at="$"):
    """Locate a first difference without flooding logs with large JSON values."""
    if type(expected) is not type(actual):
        return f"{at}: types {type(expected).__name__} and {type(actual).__name__}"
    if isinstance(expected, dict):
        if expected.keys() != actual.keys():
            missing = sorted(set(expected) - set(actual))
            extra = sorted(set(actual) - set(expected))
            return f"{at}: missing keys {missing}; extra keys {extra}"
        for key in expected:
            found = first_difference(expected[key], actual[key], at + "." + key)
            if found:
                return found
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            return f"{at}: lengths {len(expected)} and {len(actual)}"
        for index, (left, right) in enumerate(zip(expected, actual)):
            found = first_difference(left, right, f"{at}[{index}]")
            if found:
                return found
    elif expected != actual:
        return f"{at}: expected {repr(expected)[:180]}, obtained {repr(actual)[:180]}"
    return None


class Reproduction:
    def __init__(self, mode: str):
        self.mode = mode
        self.started = time.monotonic()
        self.output_root = ROOT / "reproduced"
        self.output_root.mkdir(exist_ok=True)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        self.run_dir = Path(tempfile.mkdtemp(
            prefix=f"{mode}-{stamp}-", dir=self.output_root))
        self.logs = self.run_dir / "logs"
        self.results = self.run_dir / "results"
        self.logs.mkdir()
        self.results.mkdir()
        self.commands = []
        self.checks = []
        self.protected = {}
        self.integrity = {}
        self.baseline_manifest = {}
        self.baseline = ROOT / "research/baseline"
        self.replay = self.run_dir / "baseline"
        self.summary = {
            "status": "RUNNING", "mode": mode,
            "python": sys.version.split()[0],
            "run_directory": self.display(self.run_dir),
            "driver_sha256": sha256(Path(__file__)),
            "packing_max_n": 3 if mode == "quick" else 4,
            "searches_replayed": mode == "searches",
            "scope": ("Finite computational reproduction only; no Lean/Rocq build, "
                      "new consistency certificate, or state-minimality result."),
        }

    def display(self, path: Path) -> str:
        try:
            return str(path.resolve().relative_to(ROOT))
        except ValueError:
            return str(path)

    def checked(self, name: str, **details):
        self.checks.append({"name": name, "status": "PASS", **details})
        print("PASS " + name, flush=True)

    def protect(self, path: Path):
        self.protected[path] = sha256(path)

    def verify_record(self, base: Path, record: dict):
        path = relative_file(base, record["local_path"])
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != record["sha256"]:
            raise VerificationError("SHA-256 mismatch: " + self.display(path))
        size = record.get("bytes", record.get("size"))
        if size is not None and len(raw) != size:
            raise VerificationError("Byte-count mismatch: " + self.display(path))
        if "git_blob_sha" in record:
            header = ("blob " + str(len(raw)) + "\0").encode("ascii")
            blob = hashlib.sha1(header + raw, usedforsecurity=False).hexdigest()
            if blob != record["git_blob_sha"]:
                raise VerificationError("Git blob mismatch: " + self.display(path))
        self.protected[path] = hashlib.sha256(raw).hexdigest()

    def verify_inputs(self):
        manifest_path = self.baseline / "manifest.json"
        self.baseline_manifest = read_json(manifest_path)
        if set(self.baseline_manifest) != BASELINE_REQUIRED:
            raise VerificationError("Baseline manifest differs from the 16-file replay interface.")
        for name, digest in self.baseline_manifest.items():
            path = relative_file(self.baseline, name)
            if sha256(path) != digest:
                raise VerificationError("Baseline input hash mismatch: " + name)
            self.protected[path] = digest
        self.protect(manifest_path)
        self.integrity["baseline_files"] = len(self.baseline_manifest)

        provenance_path = ROOT / "provenance/proveit_sources.json"
        provenance = read_json(provenance_path)
        entries = provenance["entries"]
        if not entries:
            raise VerificationError("The ProveIt source inventory is empty.")
        for entry in entries:
            self.verify_record(ROOT, entry)
        self.protect(provenance_path)
        self.integrity["proveit_source_files"] = len(entries)
        self.integrity["proveit_pin"] = provenance["pin"]

        bridge = ROOT / "research/bridge"
        contract_path = bridge / "bridge_contract.json"
        contract = read_json(contract_path)
        for entry in contract["sources"]:
            self.verify_record(bridge, entry)
        licenses = contract["source_snapshot"]["licenses"]
        for entry in licenses:
            self.verify_record(bridge, entry)
        self.protect(contract_path)
        self.integrity["bridge_source_files"] = len(contract["sources"])
        self.integrity["bridge_license_files"] = len(licenses)
        if sha256(self.baseline / TABLE_REL) != contract["machine_sha256"]:
            raise VerificationError("Bridge contract and literal machine identities differ.")

        # Also ensure the scripts, fixtures and positive certificates used
        # below are preserved, beyond the explicitly pinned source inventory.
        for folder in ("bridge", "theory", "packing"):
            for path in (ROOT / "research" / folder).iterdir():
                if path.is_file() and path.suffix in {".py", ".json", ".bits"}:
                    self.protect(path)
        self.checked("source_integrity", **self.integrity)

    def copy_baseline(self):
        self.replay.mkdir()
        for name in self.baseline_manifest:
            destination = self.replay / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.baseline / name, destination)
        shutil.copyfile(self.baseline / "manifest.json", self.replay / "manifest.json")

    def command(self, label: str, script: Path, *arguments, isolated=False,
                stdout_json: Path | None = None):
        argv = [sys.executable]
        if isolated:
            argv.append("-I")
        argv += ["-B", str(script), *(str(arg) for arg in arguments)]
        prefix = f"{len(self.commands) + 1:02d}_{label}"
        stdout_path = self.logs / (prefix + ".stdout.log")
        stderr_path = self.logs / (prefix + ".stderr.log")
        record = {"name": label, "argv": argv, "cwd": str(ROOT),
                  "stdout": self.display(stdout_path),
                  "stderr": self.display(stderr_path)}
        self.commands.append(record)
        write_json(self.logs / "commands.json", self.commands)
        environment = os.environ.copy()
        # -B prevents cache writes; retaining the script directory is needed
        # for closure_reference.py's sibling finite_bridge import.
        for name in ("PYTHONOPTIMIZE", "PYTHONPATH", "PYTHONHOME"):
            environment.pop(name, None)
        start = time.monotonic()
        print("RUN  " + label, flush=True)
        try:
            with stdout_path.open("wb") as out, stderr_path.open("wb") as err:
                completed = subprocess.run(
                    argv, cwd=ROOT, env=environment, stdout=out, stderr=err,
                    check=False)
            record["returncode"] = completed.returncode
        finally:
            record["elapsed_seconds"] = round(time.monotonic() - start, 6)
            write_json(self.logs / "commands.json", self.commands)
        if completed.returncode:
            raise VerificationError(
                f"{label} exited {completed.returncode}; see {self.display(stderr_path)}")
        if stdout_json is not None:
            try:
                parsed = read_json(stdout_path)
            except json.JSONDecodeError as exc:
                raise VerificationError(
                    f"{label} did not emit one JSON document: {exc}") from exc
            write_json(stdout_json, parsed)

    def compare(self, name: str, expected, actual, **details):
        difference = first_difference(expected, actual)
        if difference:
            raise VerificationError(name + " differs: " + difference)
        self.checked(name, **details)

    def compare_files(self, name: str, expected: Path, actual: Path):
        self.compare(name, read_json(expected), read_json(actual),
                     comparison="complete parsed JSON")

    def basic_checks(self):
        self.copy_baseline()
        self.command("literal_253_generator",
                     self.replay / "busy-beaver/ZF/m253/tools/generate_candidate.py",
                     "--check", isolated=True)
        self.checked("literal_253_four_edit_reconstruction")
        self.command("stored_mixed_summary", self.replay / "summarize_mixed.py",
                     isolated=True)
        self.compare_files("stored_mixed_evidence_summary",
                           self.baseline / "mixed_merge_summary.json",
                           self.replay / "mixed_merge_summary.json")

        bridge = ROOT / "research/bridge"
        finite = self.results / "finite_bridge.json"
        self.command("finite_bridge", bridge / "finite_bridge.py",
                     "--machine", self.baseline / TABLE_REL,
                     "--steps", "312975", stdout_json=finite)
        self.compare_files("finite_bridge_and_312975_step_boot",
                           bridge / "bridge_results.json", finite)

        certificates = {}
        for variant in ("epsc", "xfp"):
            output = self.results / f"closure_{variant}.json"
            certificate = self.results / f"empty_object_{variant}.bits"
            self.command("closure_" + variant, bridge / "closure_reference.py",
                         "--variant", variant, "--fixed-axiom", "adjunction",
                         "--self-test", "--output", output,
                         "--emit-empty-certificate", certificate)
            expected = bridge / ("closure_reference_results.json" if variant == "epsc"
                                 else "closure_reference_xfp_results.json")
            self.compare_files("closure_reference_" + variant, expected, output)
            certificates[variant] = certificate

        cert_checker = self.run_dir / "check_saved_certificates.py"
        cert_checker.write_text(CERTIFICATE_CHECK, encoding="utf-8")
        cert_result = self.results / "saved_certificates.json"
        self.command("saved_positive_certificates", cert_checker, bridge,
                     bridge / "empty_object_certificate.bits", certificates["epsc"],
                     bridge / "empty_object_xfp_certificate.bits", certificates["xfp"],
                     stdout_json=cert_result)
        self.compare("saved_positive_certificates", {
            "epsc": {"bits": 4087, "nodes": 20, "accepted": True, "is_refutation": False},
            "xfp": {"bits": 5404, "nodes": 21, "accepted": True, "is_refutation": False},
        }, read_json(cert_result), comparison="saved raw bytes and proof acceptance")

        theory = ROOT / "research/theory"
        metrics = self.results / "formula_metrics.json"
        self.command("formula_metrics", theory / "formula_metrics.py", "--output", metrics)
        self.compare_files("formula_metrics", theory / "formula_metrics.json", metrics)
        hulls = self.results / "least_hulls.json"
        self.command("least_hulls", theory / "least_hull_check.py",
                     "--max-vertices", "3", "--output", hulls)
        self.compare_files("least_hull_graphs_n3", theory / "least_hull_results.json", hulls)

        packing = ROOT / "research/packing"
        bound = 3 if self.mode == "quick" else 4
        output = self.results / f"observational_packing_n{bound}.json"
        self.command("observational_packing", packing / "observational_packing.py",
                     "--max-n", bound, "--output", output)
        expected = read_json(packing / "observational_packing_results.json")
        actual = read_json(output)
        if bound == 4:
            self.compare("observational_packing_n4", expected, actual,
                         comparison="complete parsed JSON")
        else:
            # Recorded n=3 census controls; the delivered n=4 result supplies
            # the identical HF and first-witness controls independently.
            selected = {
                "graphs": 530,
                "atomic_congruence_comparisons": 4970,
                "ordered_pair_witnesses": 1312,
                "pair_matrix_local_bounds": 13954,
                "short_profile_singleton_checks": 1689,
            }
            obtained = {key: actual["counts"].get(key) for key in selected}
            self.compare("observational_packing_n3_counts", selected, obtained,
                         comparison="selected recorded n=3 census counts")
            controls = ("hereditarily_finite_tuple_controls", "incoming_profile_counterexample",
                        "nontrivial_ordered_pair_witness", "scope",
                        "mathematical_theorems_claimed_by_test")
            self.compare("observational_packing_shared_controls",
                         {key: expected[key] for key in controls},
                         {key: actual[key] for key in controls})
            if actual.get("max_n") != 3:
                raise VerificationError("Quick packing did not use max_n=3.")

    def search_checks(self):
        for radius, bound in ((4, 64), (6, 128)):
            filename = f"public253_macro_r{radius}.json"
            expected = read_json(self.baseline / filename)
            provenance = expected["input"]
            args = [
                self.replay / TABLE_REL,
                "--expected-sha256", provenance["sha256"],
                "--expected-states", "253", "--expected-halt", "253",
                "--source-commit", provenance["source_commit"],
                "--source-url", provenance["source_url"],
                "--window-radius", str(radius), "--macro-steps", str(bound),
                "--output", self.replay / filename,
            ]
            if radius == 4:
                args += ["--trace-steps", "312975", "--self-test"]
            self.command(f"macro_radius_{radius}", self.replay / "audit_tm.py",
                         *args, isolated=True)
            self.compare(f"macro_radius_{radius}", expected,
                         read_json(self.replay / filename), comparison="complete parsed JSON")

        self.command("mixed_row_search", self.replay / "mixed_merge_search.py",
                     "--fuel", "1000", isolated=True)
        self.command("regenerated_mixed_summary", self.replay / "summarize_mixed.py",
                     isolated=True)
        expected = read_json(self.baseline / "mixed_merge_summary.json")
        actual = read_json(self.replay / "mixed_merge_summary.json")
        for item in (expected, actual):
            item.pop("raw_results_sha256")
        self.compare("regenerated_mixed_summary", expected, actual,
                     comparison="complete summary except regenerated raw-file digest")

        expected = read_json(self.baseline / "mixed_merge_results.json")
        actual = read_json(self.replay / "mixed_merge_results.json")
        for item in (expected, actual):
            item.pop("elapsed_seconds")
            for candidate in item["candidates"]:
                if "rows" in candidate:
                    candidate["rows"].sort()
        self.compare("all_normalized_mixed_candidates", expected, actual,
                     comparison="all fields except elapsed time and protected-row order",
                     construction_choices=len(actual["candidates"]))

    def preserved_inputs(self):
        for path, digest in self.protected.items():
            if sha256(path) != digest:
                raise VerificationError("A source input changed during replay: " + self.display(path))
        self.checked("source_evidence_preserved", files=len(self.protected))

    def finish(self, status: str, error: str | None = None):
        self.summary.update(
            status=status, input_integrity=self.integrity, checks=self.checks,
            commands_executed=len(self.commands),
            elapsed_seconds=round(time.monotonic() - self.started, 6),
            command_log=self.display(self.logs / "commands.json"),
        )
        if error is not None:
            self.summary["error"] = error
        write_json(self.run_dir / "verification_summary.json", self.summary)
        write_json(self.output_root / "verification_summary.json", self.summary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--quick", action="store_const", dest="mode", const="quick",
                       help="default: finite interfaces, n=3 packing, and stored evidence")
    modes.add_argument("--full", action="store_const", dest="mode", const="full",
                       help="quick checks with the complete n=4 packing census")
    modes.add_argument("--searches", action="store_const", dest="mode", const="searches",
                       help="full checks plus both macro and mixed-row search replays")
    parser.set_defaults(mode="quick")
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.error("Python 3.10 or later is required.")
    if sys.flags.optimize:
        parser.error("Run without -O; attributed input checks require assertions.")
    replay = Reproduction(args.mode)
    try:
        replay.verify_inputs()
        replay.basic_checks()
        if args.mode == "searches":
            replay.search_checks()
        replay.preserved_inputs()
    except KeyboardInterrupt:
        replay.finish("INTERRUPTED", "Interrupted by the operator.")
        print("INTERRUPTED; partial logs retained at " + replay.display(replay.run_dir),
              file=sys.stderr)
        return 130
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        replay.finish("FAIL", str(exc))
        print("FAIL " + str(exc), file=sys.stderr)
        print("Summary: " + replay.display(replay.output_root / "verification_summary.json"),
              file=sys.stderr)
        return 1
    replay.finish("PASS")
    print("PASS all requested finite checks; summary: " +
          replay.display(replay.output_root / "verification_summary.json"), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
