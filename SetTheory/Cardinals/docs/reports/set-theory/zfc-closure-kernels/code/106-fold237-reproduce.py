#!/usr/bin/env python3
"""Replay the delivered 237-state construction without changing its evidence.

Requires Python 3.10+ and the standard library; run without -O or -OO.
The default replay performs fresh finite checks and audits the delivered full
runtime certificates. Add --full to rerun all three unbounded symbolic jobs.
Every checker runs in a fresh temporary package copy. Output contains command
arrays, logs, replayed receipts and a final replay.json; original evidence is
never overwritten.
"""

from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import traceback


ROOT = Path(__file__).resolve().parent
SOURCE_HASH = "7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6"
TABLE_HASHES = {
    "zfc_composed238_old.tm": "069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c",
    "zfc_composed238.tm": "909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08",
    "zfc_composed237_old.tm": "a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a",
    "zfc_composed237.tm": "7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6",
    "inputs/zfc_boundary239_old.tm": "d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719",
    "inputs/boundary240_old.tm": "19cd7f7863a681828fd026adbf8ce91c21e3ac7604439bc9d4603ba58661853e",
}
CASE_HASHES = {
    "universal_runtime238_cases.json": "878ed9d459867d6af94d55250f444e02c26c0b795d99d06e5dd1f560c2886cbf",
    "universal_runtime237_cases.json": "573e2d88400030c9457ab028c701102205124875f69aedd6acfa7f9341cd8c25",
    "boundary_guard_cases.json": "606c4d8e003120583774840e64e4f9dd7d46f0bcaae7c47a053e3f9d5c4b0b62",
    "boundary_guard_visits.json": "c5cf7aa851b95af94f36df2357f4ff3d03a2da0d8c66e3376573d3a3a00d6fea",
}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".writing")
    temporary.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def stable(value):
    """Remove operational metadata; preserve every mathematical proof field."""
    if isinstance(value, list):
        return [stable(item) for item in value]
    if isinstance(value, dict):
        excluded = {"seconds", "elapsed_seconds", "wall_time_seconds", "execution", "argv", "python_version", "python_executable"}
        path_keys = {"baseline", "candidate", "output", "output_dir"}
        return {key: stable(item) for key, item in value.items()
                if key not in excluded and not (key in path_keys and isinstance(item, str))}
    return value


def stable_digest(value):
    raw = json.dumps(stable(value), sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def manifest_check(root):
    manifest = root / "SHA256SUMS"
    if not manifest.exists():
        return {"status": "NOT_PRESENT", "checked_files": 0}
    checked = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64}) [ *](.+)", line)
        require(match is not None, ("Malformed SHA256SUMS line", line))
        expected, name = match.groups()
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts, ("Unsafe manifest path", name))
        target = (root / relative).resolve()
        require(target.is_relative_to(root.resolve()) and target.is_file(), ("Missing manifest file", name))
        require(name not in checked, ("Duplicate manifest entry", name))
        actual = digest(target)
        require(actual == expected.lower(), ("Manifest mismatch", name, expected, actual))
        checked[name] = actual
    require(checked, "SHA256SUMS contains no entries")
    require("reproduce.py" in checked and "build_composed237.py" in checked,
            "SHA256SUMS must include both reproduction programs")
    return {"status": "PASS", "checked_files": len(checked), "sha256": digest(manifest)}


def table_rows(path):
    rows = set()
    for line in path.read_text(encoding="ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        match = re.fullmatch(r"(\d+) ([01]) ([01]) ([LR]) (\d+)", line)
        require(match is not None, ("Malformed table", path.name, line))
        key = int(match[1]), int(match[2])
        require(key not in rows, ("Duplicate table row", path.name, key))
        rows.add(key)
    return sorted([q, b] for q, b in rows)


def inspect_case_array(root, filename, expected_steps, sites):
    path = root / "evidence" / filename
    require(digest(path) == CASE_HASHES[filename], ("Delivered case bytes changed", filename))
    cases = read_json(path)
    expected = [(i, positive) for i, site in enumerate(sites)
                for positive in ((False, True) if site[1] == "CD" else (False,))]
    require(len(cases) == len(expected) == 8386, ("Incomplete case array", filename))
    for case, (index, positive) in zip(cases, expected):
        require(type(case["site_index"]) is int and type(case["positive"]) is bool,
                ("Malformed case key", filename))
        require((case["site_index"], case["positive"]) == (index, positive),
                ("Case order or coverage changed", filename, index, positive))
        require(type(case["symbolic_steps"]) is int and case["symbolic_steps"] > 0,
                ("Invalid symbolic step count", filename, index))
        duration, motion = case["duration"], case["motion"]
        require(len(duration) == len(motion) == 13, ("Malformed affine vector", filename, index))
        require(all(type(x) is int and x >= 0 for x in duration) and duration[0] >= 1,
                ("Invalid positive clock", filename, index))
        require(all(type(x) is int for x in motion), ("Malformed motion vector", filename, index))
        require(set(case["kinds"]) <= {"literal", "unary", "list"}, "Unknown rule kind")
        require(all(type(n) is int and n >= 0 for n in case["kinds"].values()), "Invalid rule-kind count")
        require(sum(case["kinds"].values()) == case["symbolic_steps"], "Rule-kind census mismatch")
    require(sum(case["symbolic_steps"] for case in cases) == expected_steps,
            ("Wrong aggregate symbolic rule count", filename))
    require(min(case["duration"][0] for case in cases) == 13, ("Wrong minimum clock", filename))
    return cases, {"file": "evidence/" + filename, "sha256": digest(path),
                   "cases": len(cases), "symbolic_rules": expected_steps,
                   "minimum_duration_constant": 13, "stable_data_sha256": stable_digest(cases)}


def audit_delivered(root):
    for name, expected in TABLE_HASHES.items():
        require(digest(root / name) == expected, ("Pinned table changed", name))
    require(digest(root / "inputs/sites_logical.json") == SOURCE_HASH, "Boundary source changed")
    sites = read_json(root / "inputs/sites_logical.json")
    require(len(sites) == 6455, "Wrong source leaf count")
    audits = []
    for states, rules in ((238, 2255513), (237, 2261369)):
        name = f"universal_runtime{states}"
        summary = read_json(root / "evidence" / (name + ".json"))
        cases, audit = inspect_case_array(root, name + "_cases.json", rules, sites)
        expected = {
            "status": "UNIVERSAL_MATHEMATICAL_PASS", "working_states": states,
            "transition_rows": 2 * states, "cases": len(cases),
            "symbolic_steps": rules, "minimum_actual_steps": 13,
            "table_sha256": digest(root / f"zfc_composed{states}_old.tm"),
            "sites_sha256": SOURCE_HASH,
            "checker_sha256": digest(root / "verification/check_literal_runtime.py"),
            "engine_sha256": digest(root / "verification/symbolic_runtime.py"),
            "helper_sha256": digest(root / "verification/independent_runtime.py"),
        }
        for key, value in expected.items():
            require(summary.get(key) == value, ("Runtime receipt mismatch", states, key))
        require(summary["directly_used_rows"] == table_rows(root / f"zfc_composed{states}_old.tm"),
                ("Incomplete literal row coverage", states))
        require(len(summary["blocks"]) == 4, "Expected four list-induction schemas")
        audit.update({"summary": "evidence/" + name + ".json", "summary_sha256": digest(root / "evidence" / (name + ".json")),
                      "summary_stable_sha256": stable_digest(summary), "literal_rows_covered": 2 * states})
        audits.append(audit)
    summary = read_json(root / "evidence/boundary_guard.json")
    cases, audit = inspect_case_array(root, "boundary_guard_cases.json", 2247513, sites)
    visits_path = root / "evidence/boundary_guard_visits.json"
    require(digest(visits_path) == CASE_HASHES[visits_path.name], "Delivered guard-visit bytes changed")
    visits = read_json(visits_path)
    expected = {
        "status": "PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD",
        "table_sha256": TABLE_HASHES["inputs/zfc_boundary239_old.tm"],
        "sites_sha256": SOURCE_HASH,
        "instrument_sha256": digest(root / "verification/certify_boundary_guard.py"),
        "engine_sha256": digest(root / "verification/guard_engine/symbolic_runtime.py"),
        "helper_sha256": digest(root / "verification/guard_engine/independent_runtime.py"),
        "cases": 8386, "symbolic_rules": 2247513,
        "minimum_instruction_duration_constant": 13, "transition_rows_covered": 478,
        "explicit_guard_visits": 32, "minimum_certified_one_run_constant": 23,
        "no_induction_hides_state169": True,
    }
    for key, value in expected.items():
        require(summary.get(key) == value, ("Guard summary mismatch", key))
    require(len(visits) == sum(c["guard_visits"] for c in cases) == 32, "Incomplete guard visits")
    actual_counts = Counter((v["site_index"], v["positive"]) for v in visits)
    require(actual_counts == Counter({(c["site_index"], c["positive"]): c["guard_visits"]
                                      for c in cases if c["guard_visits"]}), "Guard visits do not match cases")
    for visit in visits:
        for key in ("one_run_length", "clock"):
            require(len(visit[key]) == 13 and all(type(n) is int and n >= 0 for n in visit[key]),
                    ("Invalid guard affine vector", key))
        require(visit["one_run_length"][0] >= 2, "Right-neighbor guard is insufficient")
    require(min(v["one_run_length"][0] for v in visits) == 23, "Wrong minimum guard run")
    prefix = read_json(root / "inputs/boundary239_blank_prefix.json")
    boot = summary["bootstrap"]
    require((boot["steps"], boot["state"], boot["head"]) == (409691, 96, -5), "Wrong guard startup")
    require(boot["ones"] == prefix["all_one_positions"] and len(boot["ones"]) == 351,
            "Guard startup tape differs from the prescribed frame")
    require(boot["all_other_cells_zero"] and boot["guard_visits"] == {"169/0": 12, "169/1": 6},
            "Guard startup inventory differs")
    audit.update({"summary": "evidence/boundary_guard.json", "summary_sha256": digest(root / "evidence/boundary_guard.json"),
                  "summary_stable_sha256": stable_digest(summary), "literal_rows_covered": 478,
                  "explicit_guard_visits": 32, "minimum_guard_one_run_constant": 23,
                  "visits_file_sha256": digest(visits_path)})
    audits.append(audit)
    return {"status": "PASS_DELIVERED_FULL_CERTIFICATE_AUDIT", "source_sha256": SOURCE_HASH,
            "scope": "Audits pinned case arrays, complete guard keys, affine clocks, checker/table hashes, row coverage and aggregate counts. Quick mode does not rerun the expensive symbolic derivations.",
            "certificates": audits}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("replay"),
                        help="new or empty output directory; default: replay")
    parser.add_argument("--full", action="store_true", help="also rerun both direct runtime proofs and the boundary guard")
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), "Python 3.10 or newer is required")
    require(__debug__ and not sys.flags.optimize, "Run without -O or -OO")
    output = args.output_dir.resolve()
    require(output != ROOT and not ROOT.is_relative_to(output), "Use a separate replay output directory")
    require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
            "Output directory must be new or empty; preserve previous replay receipts")
    output.mkdir(parents=True, exist_ok=True)
    (output / "logs").mkdir()
    record = {"status": "RUNNING", "mode": "full" if args.full else "quick",
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "python_version": sys.version, "python_executable": sys.executable,
              "assertions_enabled": True, "temporary_copy": True,
              "commands": [], "comparisons": [], "replayed_receipts": []}
    started = time.monotonic()
    tracked = {str(p.relative_to(ROOT)): digest(p) for p in (ROOT / "evidence").glob("*.json")}
    def save():
        write_json(output / "replay.json", record)
    save()
    try:
        record["manifest"] = manifest_check(ROOT)
        record["delivered_full_certificate_audit"] = audit_delivered(ROOT)
        save()
        with tempfile.TemporaryDirectory(prefix="zfc237-replay-") as temporary:
            work = Path(temporary) / "package"
            def ignore(directory, names):
                ignored = {name for name in names if name in {"__pycache__", ".git"} or name.endswith(".pyc")}
                for name in names:
                    if (Path(directory) / name).resolve() == output:
                        ignored.add(name)
                return ignored
            shutil.copytree(ROOT, work, ignore=ignore)
            products = work / "replay_products"
            (products / "receipts").mkdir(parents=True)
            environment = os.environ.copy()
            environment["PYTHONOPTIMIZE"] = "0"
            environment["PYTHONDONTWRITEBYTECODE"] = "1"
            def run(name, arguments):
                number = len(record["commands"]) + 1
                log_name = f"{number:02d}_{name}.log"
                command = [sys.executable, "-B", *arguments]
                item = {"name": name, "command": command, "cwd": "fresh temporary package copy",
                        "log": "logs/" + log_name, "status": "RUNNING"}
                record["commands"].append(item)
                save()
                print("RUN", name, flush=True)
                tick = time.monotonic()
                with (output / "logs" / log_name).open("w", encoding="utf-8") as log:
                    process = subprocess.Popen(command, cwd=work, env=environment, stdout=log, stderr=subprocess.STDOUT)
                    while True:
                        try:
                            code = process.wait(timeout=30)
                            break
                        except subprocess.TimeoutExpired:
                            print("RUNNING", name, round(time.monotonic() - tick), "seconds", flush=True)
                item.update({"returncode": code, "seconds": time.monotonic() - tick,
                             "log_sha256": digest(output / "logs" / log_name),
                             "status": "PASS" if code == 0 else "FAIL"})
                save()
                require(code == 0, ("Checker failed", name, item["log"]))
            def compare_json(fresh, delivered, label):
                a, b = read_json(fresh), read_json(delivered)
                require(stable(a) == stable(b), ("Deterministic proof fields changed", label))
                record["comparisons"].append({"name": label, "status": "PASS", "stable_sha256": stable_digest(a)})
            def receipt(relative, delivered=None):
                fresh = work / relative
                require(fresh.is_file(), ("Missing replayed receipt", relative))
                value = read_json(fresh)
                if isinstance(value, dict):
                    status = value.get("status", "")
                    require(status.startswith("PASS") or status.endswith("PASS"), ("Nonpassing receipt", relative, status))
                if delivered is not None:
                    compare_json(fresh, ROOT / delivered, delivered)
                destination = output / "receipts" / fresh.name
                destination.parent.mkdir(exist_ok=True)
                shutil.copy2(fresh, destination)
                record["replayed_receipts"].append({"file": "receipts/" + fresh.name, "sha256": digest(destination)})
            def identical(fresh, delivered, label):
                require(fresh.read_bytes() == delivered.read_bytes(), ("Rebuilt bytes differ", label))
                record["comparisons"].append({"name": label, "status": "PASS_BYTE_IDENTITY", "sha256": digest(fresh)})

            run("construct238", ["build_composed238.py"])
            for filename in ("zfc_composed238_old.tm", "zfc_composed238.tm", "renumbering238.json"):
                identical(work / filename, ROOT / filename, filename)
            for filename in ("construction238.json", "local_fold238.json", "bootstrap238.json"):
                receipt("evidence/" + filename, "evidence/" + filename)
            run("construct237", ["build_composed237.py", "--input238", "zfc_composed238_old.tm",
                                 "--output-dir", "replay_products/rebuilt237"])
            for filename in ("zfc_composed237_old.tm", "zfc_composed237.tm", "renumbering.json"):
                identical(products / "rebuilt237" / filename, ROOT / filename, filename)
            shutil.copytree(products / "rebuilt237", output / "rebuilt237")
            run("bootstrap237", ["verify_bootstrap237.py"])
            receipt("evidence/bootstrap237.json", "evidence/bootstrap237.json")
            run("source_rotation_certificate", ["source_certificate/check_rotation_certificate.py", "--report", "replay_products/receipts/source_rotation.json"])
            receipt("replay_products/receipts/source_rotation.json", "source_certificate/rotation_certificate_results.json")
            run("source_interface", ["source_interface/check_source_interface.py", "--sites", "source_certificate/baseline_sites.json",
                                     "--blank-prefix", "inputs/boundary239_blank_prefix.json", "--output", "replay_products/receipts/source_interface.json"])
            receipt("replay_products/receipts/source_interface.json")
            run("independent_source_graph", ["verification/check_source_graph.py", "source_certificate/baseline_sites.json",
                                             "inputs/sites_logical.json", "--output", "replay_products/receipts/source_graph_audit.json"])
            receipt("replay_products/receipts/source_graph_audit.json", "evidence/source_graph_audit.json")
            run("boundary240_to239", ["verification/certify_boundary_fold.py", "inputs/boundary240_old.tm",
                                      "inputs/zfc_boundary239_old.tm", "--output", "replay_products/receipts/boundary_fold.json"])
            receipt("replay_products/receipts/boundary_fold.json")
            run("independent238", ["verification/verify_composed238_independent.py", "--old", "inputs/zfc_boundary239_old.tm",
                                   "--new", "zfc_composed238_old.tm", "--output", "replay_products/receipts/composed238_independent.json"])
            receipt("replay_products/receipts/composed238_independent.json", "evidence/composed238_independent.json")
            run("local237", ["verification/verify_237.py", "--old", "zfc_composed238_old.tm", "--new", "zfc_composed237_old.tm",
                              "--output", "replay_products/receipts/local_simulation237.json"])
            receipt("replay_products/receipts/local_simulation237.json", "evidence/local_simulation237.json")
            run("independent_local237", ["verification/review_local237.py", "zfc_composed238_old.tm", "zfc_composed237_old.tm",
                                          "--output", "replay_products/receipts/local237_independent_review.json"])
            receipt("replay_products/receipts/local237_independent_review.json", "evidence/local237_independent_review.json")
            if args.full:
                full = products / "full"
                full.mkdir()
                for states in (238, 237):
                    name = f"universal_runtime{states}"
                    run(name, ["verification/check_literal_runtime.py", "--table", f"zfc_composed{states}_old.tm",
                               "--sites", "inputs/sites_logical.json", "--states", str(states),
                               "--output", "replay_products/full/" + name + ".json"])
                    receipt("replay_products/full/" + name + ".json", "evidence/" + name + ".json")
                    fresh_cases = full / (name + "_cases.json")
                    delivered_cases = ROOT / "evidence" / (name + "_cases.json")
                    compare_json(fresh_cases, delivered_cases, name + " all 8386 deterministic cases")
                    identical(fresh_cases, delivered_cases, name + " case-array bytes")
                run("boundary_guard", ["verification/certify_boundary_guard.py", "--table", "inputs/zfc_boundary239_old.tm",
                                       "--sites", "inputs/sites_logical.json", "--engine-dir", "verification/guard_engine",
                                       "--output-dir", "replay_products/full/guard"])
                receipt("replay_products/full/guard/boundary_guard.json", "evidence/boundary_guard.json")
                for filename in ("boundary_guard_cases.json", "boundary_guard_visits.json"):
                    compare_json(full / "guard" / filename, ROOT / "evidence" / filename, filename)
                    identical(full / "guard" / filename, ROOT / "evidence" / filename, filename + " bytes")
                shutil.copytree(full, output / "full")
            record["temporary_copy_removed_on_exit"] = True
        for relative, old_hash in tracked.items():
            require(digest(ROOT / relative) == old_hash, ("Original delivered evidence changed", relative))
        record.update({"status": "PASS_FULL_REPLAY" if args.full else "PASS_QUICK_REPLAY",
                       "original_evidence_unchanged": True, "original_evidence_files_checked": len(tracked),
                       "full_symbolic_jobs_rerun": 3 if args.full else 0})
    except Exception as error:
        record.update({"status": "FAIL", "error": str(error), "traceback": traceback.format_exc()})
        print("FAIL", str(error), file=sys.stderr, flush=True)
    finally:
        record["seconds"] = time.monotonic() - started
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
    print(record["status"], str(output / "replay.json"), flush=True)
    return 0 if record["status"].startswith("PASS") else 1


if __name__ == "__main__":
    raise SystemExit(main())
