#!/usr/bin/env python3
"""Offline release verification using only Python's standard library.

The component checks run in an isolated temporary copy, so this command
does not rewrite the delivered files. These finite checks are not a proof
of consistency and do not substitute for the unbounded mathematical proofs.
No acceptance criterion depends on Python's assert statement.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def release_paths():
    return sorted(p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
                  if p.is_file() and p.name != "MANIFEST.json"
                  and "__pycache__" not in p.parts
                  and p.suffix != ".pyc")


def authenticate_release():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    entries = manifest["files"]
    require(sorted(entries) == release_paths(),
            "Release manifest does not cover exactly the delivered files")
    for relative, entry in entries.items():
        raw = (ROOT / relative).read_bytes()
        require(len(raw) == entry["bytes"], "File size: " + relative)
        require(digest(raw) == entry["sha256"], "File SHA256: " + relative)
    baseline = json.loads((ROOT / "BASELINE.json").read_text())
    for entry in baseline["files"]:
        raw = (ROOT / entry["local_path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode()
                            + b"\0" + raw).hexdigest()
        require(digest(raw) == entry["sha256"], "Baseline SHA256")
        require(blob == entry["git_blob_sha1"], "Baseline Git blob")
    require(baseline["commit"] ==
            "9cca523d9f27ad39d52993f4065cbd7e58f8bdd4", "Source pin")
    for name in ("beta.bin.gz", "K.bin.gz", "MC.bin.gz", "MF_source.bin.gz"):
        require((ROOT / "positive" / "coefficients" / name).read_bytes() ==
                (ROOT / "eleven" / "coefficients" / name).read_bytes(),
                "The two positive components must use the identical tuple: " + name)
    return baseline["commit"]


def artifact_paths():
    paths = list((ROOT / "integer").glob("*.json"))
    paths += list((ROOT / "positive").glob("p*_positive_*.json"))
    paths += list((ROOT / "eleven").glob("p*_positive_*.json"))
    for component in ("integer", "positive", "eleven"):
        paths += list((ROOT / component / "coefficients").glob("*"))
    return sorted(p.relative_to(ROOT) for p in paths if p.is_file())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--optimized", action="store_true",
                        help="run all component checkers with Python -O")
    args = parser.parse_args()
    pin = authenticate_release()
    original = {p.as_posix(): (ROOT / p).read_bytes()
                for p in artifact_paths()}
    commands = ["integer/build_verify.py",
                "integer/independent_literal_audit.py",
                "positive/verify.py",
                "positive/independent_audit.py",
                "eleven/verify.py",
                "eleven/independent_audit.py"]
    checks = []
    with tempfile.TemporaryDirectory(prefix="diophantine-offline-check-") as folder:
        work = Path(folder) / "release"
        shutil.copytree(ROOT, work,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        environment = dict(os.environ)
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        environment["PYTHONHASHSEED"] = "0"
        environment["PYTHONOPTIMIZE"] = "1" if args.optimized else "0"
        for relative in commands:
            script = work / relative
            command = [sys.executable]
            if args.optimized:
                command.append("-O")
            command.append(str(script))
            result = subprocess.run(command, cwd=script.parent,
                                    env=environment, text=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, timeout=180)
            if result.returncode:
                print(result.stdout, file=sys.stderr)
                print(result.stderr, file=sys.stderr)
                raise ValueError("Component check failed: " + relative)
            # These checkers emit structured receipts as their entire stdout.
            receipt = json.loads(result.stdout)
            checks.append({"checker": relative, "status": "passed",
                           "receipt_sha256": digest(result.stdout.encode()),
                           "receipt": receipt})
        for relative, raw in original.items():
            require((work / relative).read_bytes() == raw,
                    "Regeneration changed a literal artifact: " + relative)
    result = {
        "status": "passed",
        "python_optimization_enabled": args.optimized,
        "source_commit": pin,
        "release_manifest_authenticated": True,
        "baseline_identities_authenticated": True,
        "positive_coefficient_tuples_identical": True,
        "isolated_relocation_check": True,
        "literal_artifacts_reproduced_or_authenticated": len(original),
        "component_checks": checks,
        "scope": "Exact finite algebra, degrees, costs, restoration identities, "
                 "source provenance, and fixed coefficient data. This is not "
                 "a consistency test or a proof-assistant certificate."
    }
    print(json.dumps(result, indent=2) + "\n", end="")


if __name__ == "__main__":
    main()
