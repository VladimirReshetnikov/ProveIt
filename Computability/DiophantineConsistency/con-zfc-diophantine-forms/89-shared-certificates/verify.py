#!/usr/bin/env python3
"""Verify this research package using only the Python standard library.

Default: run all independent arithmetic audits in normal and optimized Python,
run the four source audits once, and verify MANIFEST.sha256 if present.
The package is not modified; audit receipts are written only in temporary
staging unless --output explicitly requests a combined receipt.

  python verify.py
  python verify.py --rebuild
  python verify.py --archive ../con_zfc_shared_certificates.zip

--rebuild regenerates equations in a temporary directory and compares them
with the delivered files. --quick runs each independent audit once instead
of twice. No option attempts to decide whether a consistency equation has
a solution; the unbounded equivalence proofs are in the article.
"""
from __future__ import annotations

import argparse
import gzip
from hashlib import sha256
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def parse_manifest(text):
    entries = {}
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64}) [ *](.+)", line)
        require(match is not None, f"Malformed manifest line {line_number}")
        expected, name = match.groups()
        path = PurePosixPath(name)
        require(not path.is_absolute() and ".." not in path.parts and "\\" not in name,
                f"Unsafe manifest path: {name}")
        require(name not in entries, f"Duplicate manifest path: {name}")
        entries[name] = expected.lower()
    require(entries, "The manifest is empty")
    return entries


def verify_manifest(required=False):
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        require(not required, "MANIFEST.sha256 is required but absent")
        return {"status": "NOT_PRESENT", "files_checked": 0}
    entries = parse_manifest(manifest.read_text(encoding="utf-8"))
    for name, expected in entries.items():
        path = ROOT / name
        require(path.is_file(), f"Manifest file is missing: {name}")
        require(path.resolve().is_relative_to(ROOT), f"Manifest file escapes package: {name}")
        require(digest(path.read_bytes()) == expected, f"Manifest hash mismatch: {name}")
    return {"status": "PASS", "files_checked": len(entries),
            "manifest_sha256": digest(manifest.read_bytes())}


def python_json(script, arguments=(), optimized=False, cwd=None):
    command = [sys.executable, "-B"]
    if optimized:
        command.append("-O")
    command += [str(script)] + [str(arg) for arg in arguments]
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONHASHSEED"] = "0"
    process = subprocess.run(command, cwd=str(cwd or ROOT), env=environment,
                             text=True, encoding="utf-8", capture_output=True,
                             timeout=240, check=False)
    require(process.returncode == 0,
            f"{script.name} failed ({process.returncode}):\n"
            + process.stdout[-2500:] + "\n" + process.stderr[-2500:])
    try:
        result = json.loads(process.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"{script.name} did not return a JSON receipt") from exc
    require(result.get("status") == "PASS", f"{script.name} did not report PASS")
    return result


def independent_checks(quick=False):
    direct = ROOT / "direct"
    coordinates = ROOT / "coordinate_family"
    checks = []
    modes = (False,) if quick else (False, True)
    for optimized in modes:
        for name, equation_directory in (
            ("direct_affine", direct),
            ("direct_small_height", direct / "small_height"),
        ):
            result = python_json(direct / "check_equation.py",
                                 ("--directory", direct,
                                  "--equation-directory", equation_directory), optimized)
            checks.append({"name": name, "optimized": optimized, "status": "PASS",
                           "polynomial": result["polynomial"],
                           "affine_restoration": result["affine_restoration"],
                           "positive_power_calls": result["positivity"]["positive_power_calls"],
                           "checker_sha256": result["checker_sha256"]})
        result = python_json(coordinates / "check_coordinate_maps.py",
                             ("--directory", coordinates), optimized)
        checks.append({"name": "integer_coordinate_maps", "optimized": optimized,
                       "status": "PASS", "results": result["results"],
                       "incoming_unimodular_bridge": result["incoming_unimodular_bridge"],
                       "checker_sha256": result["checker_sha256"]})
    return checks


def source_checks():
    """Run source checks without overwriting any delivered audit receipt."""
    direct = ROOT / "direct"
    checks = []
    with tempfile.TemporaryDirectory(prefix="con_zfc_source_audit_") as temporary:
        staging = Path(temporary)

        # This audit has no output option and writes next to __file__.  It
        # reads only the adjacent source JSON, so stage exact copies of both.
        # The executable code and numerical input are unchanged.
        for filename in ("audit_calculus.py", "wire_eliminated_source.json"):
            shutil.copyfile(direct / filename, staging / filename)
        result = python_json(staging / "audit_calculus.py", cwd=staging)
        checks.append({"name": "numerical_calculus_identities", "status": "PASS",
                       "checker_sha256": digest((direct / "audit_calculus.py").read_bytes()),
                       "receipt": result})

        for name, filename in (
            ("source_wire_elimination", "audit_source.py"),
            ("literal_calculus_controls", "audit_literal.py"),
            ("positive_power_graph_identities", "audit_power_graph.py"),
        ):
            result = python_json(direct / filename,
                                 ("--output", staging / (name + ".json")))
            checks.append({"name": name, "status": "PASS",
                           "checker_sha256": digest((direct / filename).read_bytes()),
                           "receipt": result})
    return checks


def compare_file(original, rebuilt):
    require(rebuilt.is_file(), f"Rebuild omitted {original.name}")
    require(original.read_bytes() == rebuilt.read_bytes(),
            f"Rebuilt file differs: {original.relative_to(ROOT)}")


def rebuild_checks():
    direct = ROOT / "direct"
    coordinates = ROOT / "coordinate_family"
    with tempfile.TemporaryDirectory(prefix="con_zfc_verify_") as temporary:
        staging = Path(temporary)
        comparisons = []
        for name, arguments, original in (
            ("direct_affine", (), direct),
            ("direct_small_height", ("--keep-linear-wires",), direct / "small_height"),
        ):
            target = staging / name
            receipt = python_json(direct / "build_equation.py",
                                  ("--source", direct / "wire_eliminated_source.json",
                                   "--output", target) + arguments)
            for filename in ("equation.json", "expanded_polynomial.json"):
                compare_file(original / filename, target / filename)
            comparisons.append({"name": name, "status": "PASS", "equation_files_compared": 2,
                                "metrics": receipt["metrics"]})

        staged_coordinates = staging / "coordinate_family"
        shutil.copytree(coordinates, staged_coordinates,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc", "*.pyo"))
        python_json(staged_coordinates / "build_family.py", cwd=staged_coordinates)
        python_json(staged_coordinates / "build_coordinate_family.py", cwd=staged_coordinates)
        equation_files = sorted((coordinates / "equations").glob("*.json"))
        for original in equation_files:
            compare_file(original, staged_coordinates / "equations" / original.name)
        payloads = sorted((coordinates / "coefficients").glob("*.bin.gz"))
        for original in payloads:
            rebuilt = staged_coordinates / "coefficients" / original.name
            require(gzip.decompress(original.read_bytes()) == gzip.decompress(rebuilt.read_bytes()),
                    "Rebuilt integer coefficient differs: " + original.name)
        comparisons.append({"name": "integer_coordinate_maps", "status": "PASS",
                            "equation_files_compared": len(equation_files),
                            "coefficient_integer_payloads_compared": len(payloads),
                            "comparison": "Exact equation bytes; decompressed coefficient bytes"})
    return comparisons


def inspect_archive(path):
    cache_parts = {"__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache"}
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)), "Archive contains duplicate member names")
        for name in names:
            parts = PurePosixPath(name).parts
            require(not PurePosixPath(name).is_absolute() and ".." not in parts,
                    "Unsafe archive member: " + name)
            require(not (set(parts) & cache_parts) and not name.endswith((".pyc", ".pyo", ".DS_Store")),
                    "Archive contains a cache file: " + name)
        require(archive.testzip() is None, "Archive CRC verification failed")
        manifests = [name for name in names if PurePosixPath(name).name == "MANIFEST.sha256"]
        require(len(manifests) <= 1, "Archive has multiple root manifests")
        checked = 0
        if manifests:
            manifest_name = manifests[0]
            prefix = manifest_name[:-len("MANIFEST.sha256")]
            entries = parse_manifest(archive.read(manifest_name).decode("utf-8"))
            for name, expected in entries.items():
                member = prefix + name
                require(member in names, "Manifest archive member is missing: " + member)
                require(digest(archive.read(member)) == expected,
                        "Manifest archive hash mismatch: " + member)
            checked = len(entries)
    return {"status": "PASS", "members": len(names), "cache_files": 0,
            "manifest_files_checked": checked, "archive_sha256": digest(path.read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--quick", action="store_true",
                        help="run each independent audit once; default also repeats under python -O")
    parser.add_argument("--rebuild", action="store_true",
                        help="rebuild equations in temporary staging and compare with shipped files")
    parser.add_argument("--require-manifest", action="store_true",
                        help="fail if MANIFEST.sha256 is absent")
    parser.add_argument("--archive", type=Path,
                        help="also check ZIP integrity, member hashes and absence of caches")
    parser.add_argument("--output", type=Path,
                        help="optionally write the JSON receipt to this explicit path")
    args = parser.parse_args()
    result = {"status": "PASS", "python": sys.version.split()[0],
              "scope": "Finite exact arithmetic and source audits; not a decision of Con(ZFC) or a new formal proof",
              "manifest": verify_manifest(args.require_manifest),
              "independent_checks": independent_checks(args.quick),
              "source_checks": source_checks(),
              "rebuild": rebuild_checks() if args.rebuild else "NOT_REQUESTED"}
    if args.archive:
        result["archive"] = inspect_archive(args.archive.resolve())
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")


if __name__ == "__main__":
    main()
