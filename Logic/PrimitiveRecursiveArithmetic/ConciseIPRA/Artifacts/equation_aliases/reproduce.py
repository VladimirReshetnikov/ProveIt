"""Check this package and reproduce its measurements and execution evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

from measure import collect

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def check_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    require(manifest.is_file(), "Missing MANIFEST.sha256")
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = ROOT / name
        require(path.is_file(), "Missing manifest member: " + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                "Checksum mismatch: " + name)
        count += 1
    return count


def check_measurements():
    current = collect()
    frozen = json.loads((ROOT / "evidence/measurements.json").read_text())
    prior = {row["path"]: row for row in frozen["programs"]}
    fields = ("tokens", "ast_nodes", "normalized_bytes", "sha256")
    for row in current["programs"]:
        require(row["path"] in prior, "Missing frozen measurement")
        for key in fields:
            require(row[key] == prior[row["path"]][key],
                    "Measurement differs: " + row["path"] + " " + key)
    return len(current["programs"])


def quick_cases():
    cases = [
        ("atomic/code/atomic_alias.py",
         "atomic/tests/compound_specialization_rank2.json", True),
        ("atomic/code/atomic_alias_small.py",
         "atomic/tests/compound_specialization_rank1.json", True),
        ("strict/checkers/bytes633.py",
         "strict/fixtures/00_compound_case_introduction_local.json", True),
        ("strict/checkers/tokens338.py",
         "strict/fixtures/14_false_float_capture.json", False),
        ("strict/checkers/ast386.py",
         "strict/fixtures/18_phase_guard_counterexample.json", False),
    ]
    for program, fixture, expected in cases:
        result = subprocess.run([sys.executable, str(ROOT / program)],
                                input=(ROOT / fixture).read_bytes(),
                                capture_output=True, timeout=30)
        accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
        require(accepted == expected, "Unexpected verdict: " + fixture)
    return len(cases)


def full_suites():
    summaries = {}
    with tempfile.TemporaryDirectory(prefix="ipra-reproduce-") as directory:
        temporary = Path(directory)
        for name in ("atomic", "strict"):
            copy = temporary / name
            shutil.copytree(ROOT / name, copy,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
            result = subprocess.run([sys.executable, str(copy / "verify.py")],
                                    cwd=copy, capture_output=True, text=True,
                                    timeout=300)
            require(result.returncode == 0,
                    name + " suite failed:\n" + result.stdout + result.stderr)
            evidence = json.loads((copy / "evidence/verification.json").read_text())
            if name == "atomic":
                summaries[name] = {
                    "standalone_executions": evidence["standalone_executions"],
                    "closed_source_compilations": len(evidence["source_compilations"]),
                    "open_compiler_cases": evidence["open_compiler_cases"],
                }
            else:
                summaries[name] = {key: evidence[key] for key in
                                   ("executions", "fixture_count", "source_checks", "failures")}
    return summaries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"python": platform.python_version(),
              "manifest_files": check_manifest(),
              "measured_modules": check_measurements()}
    if args.quick:
        result["quick_executions"] = quick_cases()
    else:
        result["suites"] = full_suites()
    result["status"] = "PASS"
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
